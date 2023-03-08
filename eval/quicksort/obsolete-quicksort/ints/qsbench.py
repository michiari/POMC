#!/usr/bin/env python3

import argparse
import platform
import os
import signal
import subprocess as sp
import re
import statistics
import joblib
from tabulate import tabulate

time_pattern = re.compile(r"Total elapsed time: .+ \(([0-9]+\.[0-9]+e[\+\-0-9]+) s\)")
mem_pattern = re.compile(r"Max memory used \(KB\): ([0-9]+)")
result_pattern = re.compile(r"Result:  ((True)|(False))")
memgc_pattern = re.compile(r'\("max_bytes_used", "([0-9]+)"\)')
pomc_pattern = re.compile(r".*\.pomc$")

if platform.system() == 'Darwin':
    time_bin = 'gtime'
else:
    time_bin = '/usr/bin/time'

def run_cmd(cmd, timeout=None):
    # Adapted from the official cpython implementation of subprocess
    with sp.Popen(cmd, stdout=sp.PIPE, stderr=sp.PIPE, start_new_session=True) as process:
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except sp.TimeoutExpired as exc:
            os.killpg(os.getpgid(process.pid), signal.SIGKILL)
            # Won't work on MS Windows
            process.wait()
            raise
        except:  # Including KeyboardInterrupt, communicate handled that.
            os.killpg(os.getpgid(process.pid), signal.SIGKILL)
            # We don't call process.wait() as .__exit__ does that for us.
            raise
        retcode = process.poll()
    return sp.CompletedProcess(process.args, retcode, stdout, stderr)

def exec_bench(fname, finite, verbose):
    print('Evaluating file', fname, '...')
    cmd = [ '/usr/bin/time'
          , '-f'
          , 'Max memory used (KB): %M'
          , 'stack'
          , 'exec'
          , 'pomc'
          , '--'
          , fname
          , '--finite' if finite else '--infinite'
          , '+RTS'
          , '-t'
          , '--machine-readable'
          , '-RTS']

    seconds = 3600
    try:
        raw_res = run_cmd(cmd, timeout=seconds)
        raw_stdout = raw_res.stdout.decode('utf-8')
        raw_stderr = raw_res.stderr.decode('utf-8')

        if verbose >= 1:
            print(raw_stdout)
        if verbose >= 2:
            print(raw_stderr)

        if raw_res.returncode != 0:
            return ( -1, -1, -2**10, 'Error')

        time_match = time_pattern.search(raw_stdout)
        mem_match = mem_pattern.search(raw_stderr)
        result_match = [r[0] for r in result_pattern.findall(raw_stdout)]
        memgc_match = memgc_pattern.search(raw_stderr)
        result = 'False' if 'False' in result_match else 'True'
        return (float(time_match.group(1)),
                int(mem_match.group(1)), int(memgc_match.group(1)),
                result)
    except sp.TimeoutExpired:
        return ( -1, -1, -2**10, 'Time Out')


def iter_bench(fname, finite, iters, verbose):
    get_column = lambda rows, i: [r[i] for r in rows]
    results = [exec_bench(fname, finite, verbose) for _ in range(0, iters)]
    times = get_column(results, 0)
    mems = get_column(results, 1)
    memgcs = get_column(results, 2)
    res = get_column(results, 3)
    l = fname.split('/')
    l = l[len(l) -1].split('-')
    exp = l[0]
    l = l[1].split('.')
    nbits = l[0]
    lenvec = l[1]
    f = l[2]
    return (exp, nbits, lenvec, f, statistics.mean(times),
            statistics.mean(mems), statistics.mean(memgcs)/(2**10),
            res[0])

def exec_all(fnames, finite, iters, jobs, verbose):
    make_row = lambda exp, nbits, lenvec, f, time, mem, memgc, res: [exp, nbits, lenvec, f, time, mem, memgc, res]
    if jobs <= 1:
        return [make_row(*iter_bench(fname, finite, iters, verbose)) for fname in fnames]
    else:
        results = joblib.Parallel(n_jobs=jobs)(joblib.delayed(iter_bench)(fname, finite, iters, verbose)
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
    header = ["Program", "Array_values_bits", "Array_length", "Formula", timeh, "Total_memory(KiB)", "GC_Memory(KiB)", "Result"]

    if ms:
        for r in results:
            r[4] *= 1000

    tabResults = tabulate(results, headers=header)
    #print(tabResults)
    text_file=open("stats/report.csv","w")
    text_file.write(tabResults)
    text_file.close()
    print("report generated and saved")


if __name__ == '__main__':
    argp = argparse.ArgumentParser()
    argp.add_argument('-f', '--finite', action='store_true', help='Only check finite execution traces (infinite-word model checking is the default)')
    argp.add_argument('-i', '--iters', type=int, default=1, help='Number of executions for each benchmark')
    argp.add_argument('-j', '--jobs', type=int, default=1, help='Maximum number of benchmarks to execute in parallel')
    argp.add_argument('-m', '--ms', action='store_true', help='Display time in milliseconds instead of seconds')
    argp.add_argument('-v', '--verbose', action='count', default=0, help='Show individual benchmark results')
    argp.add_argument('benchmarks', type=str, nargs='+', help='*.pomc files or directories containing them')
    args = argp.parse_args()

    print('Running benchmarks...')
    results = exec_all(expand_files(args.benchmarks), args.finite, args.iters, args.jobs, args.verbose)
    pretty_print(results, args.ms)
