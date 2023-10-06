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
result_pattern = re.compile(r"Result:  ((True)|(False)|(Sat)|(Unsat)|(Unknown))")
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
            'pomc',
            '--',
            fname,
            '--finite' if args.finite else '--infinite',
            '--smt={:d}'.format(args.smt) if args.smt > 0 else '--smt=0',
            '+RTS',
            '-t',
            '--machine-readable',
            '-RTS'
        ],
        capture_output=True
    )
    raw_stdout = raw_res.stdout.decode('utf-8')
    raw_stderr = raw_res.stderr.decode('utf-8')
    if args.verbose >= 1:
        print(raw_stdout)
    if args.verbose >= 2:
        print(raw_stderr)

    if raw_res.returncode != 0:
        if raw_res.returncode == -9:
            return (-1, -1, -2**10, 'TO', -1)
        elif raw_res.returncode == 137:
            return (-1, -1, -2**10, 'OOM', -1)
        return (-1, -1, -2**10, 'Error {:d}'.format(raw_res.returncode), -1)

    time_match = time_pattern.search(raw_stdout)
    mem_match = mem_pattern.search(raw_stderr)
    result_match = [r[0] for r in result_pattern.findall(raw_stdout)]
    states_match = states_pattern.search(raw_stdout)
    memgc_match = memgc_pattern.search(raw_stderr)
    result = result_match[0]
    states = int(states_match.group(1)) if states_match else '?'
    return (
        float(time_match.group(1)),
        int(mem_match.group(1)),
        int(memgc_match.group(1)),
        result,
        states
    )

def iter_bench(fname, args):
    get_column = lambda rows, i: [r[i] for r in rows]
    results = [exec_bench(fname, args) for _ in range(0, args.iters)]
    times = get_column(results, 0)
    mems = get_column(results, 1)
    memgcs = get_column(results, 2)
    res = get_column(results, 3)
    states = get_column(results, 4)
    return (
        fname,
        statistics.mean(times),
        statistics.mean(mems),
        statistics.mean(memgcs)/(2**10),
        res[0],
        states[0]
    )

def exec_all(fnames, args, show_states):
    if show_states:
        make_row = lambda fname, time, mem, memgc, res, states: [fname, states, time, mem, memgc, res]
    else:
        make_row = lambda fname, time, mem, memgc, res, _: [fname, time, mem, memgc, res]

    if args.jobs <= 1:
        return [make_row(*iter_bench(fname, args)) for fname in fnames]
    else:
        results = joblib.Parallel(n_jobs=args.jobs)(joblib.delayed(iter_bench)(fname, args)
                                                    for fname in fnames)
        return [make_row(*res) for res in results]

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

def pretty_print(results, ms, show_states, csvfile):
    timeh = "Time (ms)" if ms else "Time (s)"
    header = ["Name"] \
        + (["# states"] if show_states else []) \
        + [timeh, "Total memory (KiB)", "GC Memory (KiB)", "Result"]

    if ms:
        idx = 2 if show_states else 1
        for r in results:
            r[idx] *= 1000

    print(tabulate(results, headers=header))

    if csvfile:
        with open(csvfile, 'w', newline='') as f:
            cw = csv.writer(f)
            cw.writerow(header)
            cw.writerows(results)


if __name__ == '__main__':
    argp = argparse.ArgumentParser()
    argp.add_argument('-f', '--finite', action='store_true', help='Only check finite execution traces (infinite-word model checking is the default)')
    argp.add_argument('-s', '--smt', type=int, default=0, help='Use the SMT-based engine with the specified trace length limit')
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
    show_states = args.state_count and args.finite and args.smt == 0

    print('Running benchmarks...')
    results = exec_all(expand_files(args.benchmarks), args, show_states)
    pretty_print(results, args.ms, show_states, args.csv)
