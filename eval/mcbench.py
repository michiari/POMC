#!/usr/bin/env python3

import argparse
import platform
import os
import subprocess
import re
import statistics
import joblib
from tabulate import tabulate
import csv

time_pattern = re.compile(r"Total elapsed time: .+ \(([0-9]+\.[0-9]+e[\+\-0-9]+) s\)")
mem_pattern = re.compile(r"Max memory used \(KB\): ([0-9]+)")
result_pattern = re.compile(r"Result:  ((True)|(False))")
states_pattern = re.compile(r"Input OPA state count: ([0-9]+)")
memgc_pattern = re.compile(r'\("max_bytes_used", "([0-9]+)"\)')
pomc_pattern = re.compile(r".*\.pomc$")

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

    raw_res = subprocess.run(
        caps_command(args.timeout, args.max_mem) +
        [
            time_bin,
            '-f',
            'Max memory used (KB): %M',
            'stack',
            'exec',
            '--',
            'pomc',
            fname,
            '--finite' if args.finite else '--infinite',
            '+RTS',
            '-t',
            '--machine-readable',
            '-RTS'
        ] + \
        (['--noovi'] if args.noovi else []),
        capture_output=True
    )
    raw_stdout = raw_res.stdout.decode('utf-8')
    raw_stderr = raw_res.stderr.decode('utf-8')
    if args.verbose >= 1:
        print(raw_stdout)
    if args.verbose >= 2:
        print(raw_stderr)

    error_dict = {
        'time': -1,
        'mem_tot': -1,
        'mem_gc': -2**10,
        'states': -1
    }
    if raw_res.returncode != 0:
        if raw_res.returncode == -9:
            return error_dict | { 'result': 'TO' }
        elif raw_res.returncode == 137:
            return error_dict | { 'result': 'OOM' }
        return error_dict | { 'result': 'Error {:d}'.format(raw_res.returncode) }

    time_match = time_pattern.search(raw_stdout)
    mem_match = mem_pattern.search(raw_stderr)
    result_match = [r[0] for r in result_pattern.findall(raw_stdout)]
    states_match = states_pattern.search(raw_stdout)
    memgc_match = memgc_pattern.search(raw_stderr)
    result = result_match[0]
    states = int(states_match.group(1)) if states_match else '?'
    return {
        'time': float(time_match.group(1)),
        'mem_tot': int(mem_match.group(1)),
        'mem_gc': int(memgc_match.group(1)),
        'result': result,
        'states': states
    }

def iter_bench(fname, args):
    get_column = lambda rows, i: [r[i] for r in rows]
    results = [exec_bench(fname, args) for _ in range(0, args.iters)]
    print(results)
    times = get_column(results, 'time')
    mems = get_column(results, 'mem_tot')
    memgcs = get_column(results, 'mem_gc')
    return {
        'name': fname,
        'time': statistics.mean(times),
        'mem_tot': statistics.mean(mems),
        'mem_gc': statistics.mean(memgcs)/(2**10),
        'result': results[0]['result'],
        'states': results[0]['states']
    }

def exec_all(fnames, args):
    if args.jobs <= 1:
        return [iter_bench(fname, args) for fname in fnames]
    else:
        return joblib.Parallel(n_jobs=args.jobs)(joblib.delayed(iter_bench)(fname, args)
                                                 for fname in fnames)

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

def to_list(results, key_map_list):
    return [[mapf(r[key]) for key, mapf in key_map_list] for r in results]

def pretty_print(results, ms, show_states, csvfile):
    idf = lambda x: x
    timeh, timef = ("Time (ms)", (lambda t: t * 1000)) if ms else ("Time (s)", idf)
    key_map_list = [('name', idf)] \
        + (['states'] if show_states else []) \
        + [
            ('time', timef),
            ('mem_tot', idf),
            ('mem_gc', idf),
            ('result', idf)
        ]
    results_matrix = to_list(results, key_map_list)

    header = ["Name"] \
        + (["# states"] if show_states else []) \
        + [timeh, "Total memory (KiB)", "GC Memory (KiB)", "Result"]

    print(tabulate(results_matrix, headers=header))

    if csvfile:
        with open(csvfile, 'w', newline='') as f:
            cw = csv.writer(f)
            cw.writerow(header)
            cw.writerows(results_matrix)


if __name__ == '__main__':
    argp = argparse.ArgumentParser()
    argp.add_argument('-f', '--finite', action='store_true', help='Only check finite execution traces (infinite-word model checking is the default)')
    argp.add_argument('-o', '--noovi', action='store_true', help='Use z3 instead of OVI to compute upper bounds')
    argp.add_argument('-i', '--iters', type=int, default=1, help='Number of executions for each benchmark')
    argp.add_argument('-j', '--jobs', type=int, default=1, help='Maximum number of benchmarks to execute in parallel')
    argp.add_argument('-t', '--timeout', type=int, default=0, help='Timeout in seconds for each benchmark. 0 = no timeout (default)')
    argp.add_argument('-M', '--max-mem', type=int, default=0, help='Maximum memory to be allocated in MiBs. 0 = no limit (default)')
    argp.add_argument('-m', '--ms', action='store_true', help='Display time in milliseconds instead of seconds')
    argp.add_argument('--state-count', action='store_true', help='Output state count when available.')
    argp.add_argument('-v', '--verbose', action='count', default=0, help='Show individual benchmark results')
    argp.add_argument('--csv', type=str, default='', help='Output result in CSV format in the specified file')
    argp.add_argument('benchmarks', type=str, nargs='+', help='*.pomc files or directories containing them')
    args = argp.parse_args()
    show_states = args.state_count and args.finite

    print('Running benchmarks...')
    results = exec_all(expand_files(args.benchmarks), args)
    pretty_print(results, args.ms, show_states, args.csv)
