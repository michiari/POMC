#!/usr/bin/env python3

import argparse
import platform
import subprocess
import re
import statistics
import joblib
import csv
from tabulate import tabulate
import os

eps_dict = {"bound-mdp-large"  : '0.000000000000001', 
            "bound-mdp-medium" : '0.0000000000001', 
            "bound-mdp-small"  : '0.0000000001',
            "mdp-medium"       : '0.000001',
            "tic-tac-toe"      : '0.000000000001',
            "mdp-small"        : '0.000001',
            "mdp-large"        : '0.0000001',
            }

time_pattern = re.compile(r"Total elapsed time: .+ \(([0-9]+\.[0-9]+e[\+\-0-9]+) s\)")
mem_pattern = re.compile(r"Max memory used \(KB\): ([0-9]+)")
#quant_result_pattern = re.compile(r"Result:  (\([0-9]+ % [0-9]+\,[0-9]+ % [0-9]+\))")
quant_result_pattern = re.compile(r"Floating Point Result:  (.*) Upper Bound Distribution:")
states_pattern = re.compile(r"Input (OPA|pOPA) state count: ([0-9]+)")
supp_pattern = re.compile(r"Support graph size: ([0-9]+)")
eqs_pattern = re.compile(r"Equations solved for termination probabilities: ([0-9]+)")
non_trivial_eqs_pattern = re.compile(r"Non-trivial equations solved for termination probabilities: ([0-9]+)")
sccs_pattern = re.compile(r"SCC count in the support graph: ([0-9]+)")
maxscc_pattern = re.compile(r"Size of the largest SCC in the support graph: ([0-9]+)")
maxeqs_pattern = re.compile(r"Largest number of non trivial equations in an SCC in the Support Graph: ([0-9]+)")

ub_pattern = re.compile(r"([0-9]+\.[0-9]+e[\+\-0-9]+) s \(upper bounds\)")
past_pattern = re.compile(r"([0-9]+\.[0-9]+e[\+\-0-9]+) s \(PAST certificates\)")
memgc_pattern = re.compile(r'\("max_bytes_used", "([0-9]+)"\)')
pomc_pattern = re.compile(r".*\.pomc$")


benchmark_pattern = re.compile(r".*/miniprob/(\S+).pomc$")

if platform.system() == 'Darwin':
    time_bin = 'gtime'
else:
    time_bin = '/usr/bin/time'

def caps_command(timeout, max_mem):
    if timeout > 0 or max_mem > 0:
        return [
            'systemd-run',
            '--quiet',
            '--user',
            '--scope',
            '-p',
            'KillSignal=SIGKILL',
            '-p',
            'MemoryMax={:d}M'.format(max_mem) if max_mem > 0 else 'MemoryMax=infinity',
            '-p',
            'MemorySwapMax=0' if max_mem > 0 else 'MemorySwapMax=infinity',
            '-p',
            'RuntimeMaxSec={:d}'.format(timeout) if timeout > 0 else 'RuntimeMaxSec=infinity'
        ]
    else:
        return []

def exec_bench(fname, args):
    print('Evaluating file', fname, '...')
    benchmark_match = benchmark_pattern.search(fname)
    check_match = lambda m, groupno=1, err=-1: m.group(groupno) if m else err 
    name = str(check_match(benchmark_match,1,"error"))
    eps = eps_dict.get(name, None)
    print(f"Found eps: {eps}")

    raw_res = subprocess.run(
        caps_command(args.timeout, args.max_mem) +
        [
            time_bin,
            '-f',
            'Max memory used (KB): %M',
            'stack',
            'exec',
            '--',
            'popalyzer',
            fname,
            '--stats',
            '+RTS',
            '-t',
            '--machine-readable',
            '-RTS'
        ] + \
        (['--noovi'] if args.noovi else []) + \
        (['--gauss'] if args.gauss else []) + \
        ([f'--eps={eps}'] if eps is not None else []),
        capture_output=True
    )
    raw_stdout = raw_res.stdout.decode('utf-8')
    raw_stderr = raw_res.stderr.decode('utf-8')
    raw_out = raw_stdout + raw_stderr
    if True:
        print(raw_stdout)
    if True:
        print(raw_stderr)

    time_match = time_pattern.search(raw_stdout)
    mem_match = mem_pattern.search(raw_stderr)
    quant_result_match = quant_result_pattern.search(raw_stdout)
    states_match = states_pattern.search(raw_out)
    supp_match = supp_pattern.search(raw_out)
    eqs_match = eqs_pattern.search(raw_out)
    non_trivial_eqs_match = non_trivial_eqs_pattern.search(raw_out)
    sccs_match = sccs_pattern.search(raw_out)
    maxscc_match = maxscc_pattern.search(raw_out)
    maxeqs_match = maxeqs_pattern.search(raw_out)
    
    ub_match = ub_pattern.search(raw_out)
    past_match = past_pattern.search(raw_out)
    memgc_match = memgc_pattern.search(raw_stderr)

    record = {
        'name': str(check_match(benchmark_match,1,name)),
        'time': float(check_match(time_match)),
        'ub_time': float(check_match(ub_match)),
        'past_time': float(check_match(past_match)),
        'mem_tot': int(check_match(mem_match)),
        'mem_gc': int(check_match(memgc_match, 1, -2**10)),
        'states': int(check_match(states_match, 2)),
        'supp_size': int(check_match(supp_match)),
        'eqs': int(check_match(eqs_match)),
        'non_trivial_eqs': int(check_match(non_trivial_eqs_match)),
        'sccs': int(check_match(sccs_match)),
        'maxscc': int(check_match(maxscc_match)),
        'maxeqs': int(check_match(maxeqs_match)),
    }

    if raw_res.returncode != 0:
        if raw_res.returncode == -9:
            return record | {'quant_result': 'TO'}
        elif raw_res.returncode in [135,137,139]:
            return record | { 'quant_result': 'OOM'}
        return record | { 'quant_result': '-' }
    return record | { 'quant_result': check_match(quant_result_match) }

def iter_bench(fname, args):
    get_column = lambda rows, i: [r[i] for r in rows]
    results = [exec_bench(fname, args) for _ in range(0, args.iters)]
    return {
        'name': results[0]['name'],
        'time': statistics.mean(get_column(results, 'time')),
        'ub_time': statistics.mean(get_column(results, 'ub_time')),
        'past_time': statistics.mean(get_column(results, 'past_time')),
        'mem_tot': statistics.mean(get_column(results, 'mem_tot')),
        'mem_gc': statistics.mean(get_column(results, 'mem_gc'))/(2**10),
        'quant_result': results[0]['quant_result'],
        'states': results[0]['states'],
        'supp_size': results[0]['supp_size'],
        'eqs': results[0]['eqs'],
        'non_trivial_eqs': results[0]['non_trivial_eqs'],
        'sccs': results[0]['sccs'],
        'maxscc': results[0]['maxscc'],
        'maxeqs': results[0]['maxeqs'],
    }

def exec_all(fnames, args):
    if args.jobs <= 1:
        return [iter_bench(fname, args) for fname in fnames]
    else:
        return joblib.Parallel(n_jobs=args.jobs)(joblib.delayed(iter_bench)(fname, args)
                                                 for fname in fnames)
def to_list(results, key_map_list):
    return [[mapf(r[key]) for key, mapf in key_map_list] for r in results]

def expand_files(arglist):
    files = []
    for arg in arglist:
        if os.path.isfile(arg):
            files.append(arg)
        else:
            for dirpath, _, filenames in os.walk(arg):
                files.extend(map(lambda fn: os.path.join(dirpath, fn),
                                 filter(pomc_pattern.match, filenames)))
    return sorted(files)

if __name__ == '__main__':
    argp = argparse.ArgumentParser()
    argp.add_argument('-o', '--noovi', action='store_true', help='Use z3 instead of OVI to compute upper bounds')
    argp.add_argument('-g', '--gauss', action='store_true', help='Use value iteration with Gauss-Seidl update for iterating fixpoint equations')
    argp.add_argument('-i', '--iters', type=int, default=1, help='Number of executions for each benchmark')
    argp.add_argument('-j', '--jobs', type=int, default=1, help='Maximum number of benchmarks to execute in parallel')
    argp.add_argument('-t', '--timeout', type=int, default=0, help='Timeout in seconds for each benchmark. 0 = no timeout (default)')
    argp.add_argument('-M', '--max_mem', type=int, default=0, help='Maximum memory to be allocated in MiBs. 0 = no limit (default)')
    argp.add_argument('-v', '--verbose', action='count', default=0, help='Show individual benchmark results')
    argp.add_argument('--raw_csv', type=str, default='', help='Output result in CSV format in the specified file')
    argp.add_argument('--print', action='store_true', help='Print results to the terminal.')
    argp.add_argument('benchmarks', type=str, nargs='+', help='*.pomc files or directories containing them')
    args = argp.parse_args()

    print(f'Running benchmarks...')
    results = exec_all(expand_files(args.benchmarks), args)

    key_list = ['name', 'states', 'supp_size', 'eqs', 'non_trivial_eqs', 'sccs', 'maxscc', 'maxeqs', 'ub_time', 'time', 'mem_tot','quant_result']
    results_matrix = to_list(results, list(map(lambda k: (k,  lambda x: x), key_list)))
    header = ["Name",  "|Q_A|", "|SG|", "|f|", "|f_NT|", "#SCC", "|SCC|max", "|f(SCC)_NT|max", "UB Time (s)", "Time (s)", "Memory (KiB)","Distr."]

    # store raw results somewhere
    if args.raw_csv:
        with open(args.raw_csv, 'w', newline='') as f:
            cw = csv.writer(f)
            cw.writerow(header)
            cw.writerows(results_matrix)

    if args.print:
        print(tabulate(results_matrix, headers=header))
    if not args.raw_csv and not args.print:
        print("Benchmarks executed correctly, no place to print them specified. Exiting...")
