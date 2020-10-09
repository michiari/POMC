#!/usr/bin/env python3

import sys
import os
import subprocess
import re
import statistics
from tabulate import tabulate

time_pattern = re.compile(r"Total elapsed time: .+ \(([0-9]+\.[0-9]+e[\+\-0-9]+) s\)")
mem_pattern = re.compile(r"Max memory used \(KB\): ([0-9]+)")
pomc_pattern = re.compile(r".*\.pomc$")

def exec_bench(fname):
    raw_res = subprocess.run(["./eval.sh", fname], capture_output=True)
    time_match = time_pattern.search(raw_res.stdout.decode('utf-8'))
    mem_match = mem_pattern.search(raw_res.stderr.decode('utf-8'))
    return (float(time_match.group(1)), int(mem_match.group(1)))

def iter_bench(fname, iters):
    results = [exec_bench(fname) for _ in range(0, iters)]
    times = [t for t, _ in results]
    mems = [m for _, m in results]
    return (statistics.mean(times), statistics.mean(mems)/1024)

def exec_all(fnames, iters):
    make_row = lambda fname, time, mem: [fname, time, mem]
    return [make_row(fname, *iter_bench(fname, iters)) for fname in fnames]

def expand_files(arglist):
    files = []
    for arg in arglist:
        if os.path.isfile(arg):
            files.append(arg)
        else:
            for dirpath, _, filenames in os.walk(arg):
                files.extend(map(lambda fn: os.path.join(dirpath, fn),
                                 filter(pomc_pattern.match, filenames)))
    return files

def pretty_print(results):
    header = ["Name", "Time (s)", "Max memory (MiB)"]
    print(tabulate(results, headers=header))

if len(sys.argv) < 2:
    print("Usage: ", sys.argv[0], " <#iters> [file.pomc [...]]")
    exit(0)


results = exec_all(expand_files(sys.argv[2:]), int(sys.argv[1]))
pretty_print(results)
