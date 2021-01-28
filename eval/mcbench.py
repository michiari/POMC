#!/usr/bin/env python3

import sys
import os
import subprocess
import re
import statistics
import joblib
from tabulate import tabulate

time_pattern = re.compile(r"Total elapsed time: .+ \(([0-9]+\.[0-9]+e[\+\-0-9]+) s\)")
mem_pattern = re.compile(r"Max memory used \(KB\): ([0-9]+)")
result_pattern = re.compile(r"Result:  ((True)|(False))")
states_pattern = re.compile(r"Input OPA state count: ([0-9]+)")
pomc_pattern = re.compile(r".*\.pomc$")

def exec_bench(fname):
    raw_res = subprocess.run(["./eval.sh", fname], capture_output=True)
    raw_stdout = raw_res.stdout.decode('utf-8')
    raw_stderr = raw_res.stderr.decode('utf-8')
    print(raw_stdout)
    print(raw_stderr)

    if raw_res.returncode != 0:
        return (-1, -1, -1024, 'Error')

    time_match = time_pattern.search(raw_stdout)
    mem_match = mem_pattern.search(raw_stderr)
    result_match = result_pattern.search(raw_stdout)
    states_match = states_pattern.search(raw_stdout)
    return (int(states_match.group(1)), float(time_match.group(1)),
            int(mem_match.group(1)), result_match.group(1))

def iter_bench(fname, iters):
    get_column = lambda rows, i: [r[i] for r in rows]
    results = [exec_bench(fname) for _ in range(0, iters)]
    states = get_column(results, 0)
    times = get_column(results, 1)
    mems = get_column(results, 2)
    res = get_column(results, 3)
    return (fname, states[0], statistics.mean(times),
            statistics.mean(mems)/1024, res[0])

def exec_all(fnames, iters, jobs):
    make_row = lambda fname, states, time, mem, res: [fname, states, time, mem, res]
    if jobs <= 1:
        return [make_row(*iter_bench(fname, iters)) for fname in fnames]
    else:
        results = joblib.Parallel(n_jobs=jobs)(joblib.delayed(iter_bench)(fname, iters)
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

def pretty_print(results, ms):
    timeh = "Time (ms)" if ms else "Time (s)"
    header = ["Name", "# states", timeh, "Max memory (MiB)", "Result"]

    if ms:
        for r in results:
            r[2] *= 1000

    print(tabulate(results, headers=header))

if len(sys.argv) < 2:
    print("Usage: ", sys.argv[0], " [-iter <#iters>] [-jobs <#jobs>] [-ms] [file.pomc [...]]\n")
    exit(0)

iters = 1
jobs = 1
ms = False
files = []
i = 1
while i < len(sys.argv):
    if sys.argv[i] == "-iter":
        iters = int(sys.argv[i+1])
        i = i + 2
    elif sys.argv[i] == "-jobs":
        jobs = int(sys.argv[i+1])
        i = i + 2
    elif sys.argv[i] == "-ms":
        ms = True
        i = i + 1
    else:
        files.append(sys.argv[i])
        i = i + 1

results = exec_all(expand_files(files), iters, jobs)
pretty_print(results, ms)
