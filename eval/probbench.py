#!/usr/bin/env python3

import argparse
from mcbench import exec_all, expand_files, to_list
from tabulate import tabulate
import csv


def pretty_print(results, csvfile):
    key_list = ['name', 'states', 'supp_size', 'eqs', 'sccs', 'maxscc', 'maxeqs', 'ub_time', 'past_time', 'gg_time', 'time', 'mem_tot', 'result']
    results_matrix = to_list(results, list(map(lambda k: (k,  lambda x: x), key_list)))

    header = ["Name", "|Q_A|", "|SG|", "|f|", "#SCC", "|SCC|max", "|f(SCC)|max", "UB Time (s)", "PAST Time (s)", "G Time (s)", "Time (s)", "Memory (KiB)", "Holds AS"]

    print(tabulate(results_matrix, headers=header))

    if csvfile:
        with open(csvfile, 'w', newline='') as f:
            cw = csv.writer(f)
            cw.writerow(key_list)
            cw.writerows(results_matrix)


if __name__ == '__main__':
    argp = argparse.ArgumentParser()
    argp.add_argument('-f', '--finite', action='store_true', help='Only check finite execution traces (infinite-word model checking is the default)')
    argp.add_argument('-o', '--noovi', action='store_true', help='Use z3 instead of OVI to compute upper bounds')
    argp.add_argument('-i', '--iters', type=int, default=1, help='Number of executions for each benchmark')
    argp.add_argument('-j', '--jobs', type=int, default=1, help='Maximum number of benchmarks to execute in parallel')
    argp.add_argument('-t', '--timeout', type=int, default=0, help='Timeout in seconds for each benchmark. 0 = no timeout (default)')
    argp.add_argument('-M', '--max-mem', type=int, default=0, help='Maximum memory to be allocated in MiBs. 0 = no limit (default)')
    argp.add_argument('-v', '--verbose', action='count', default=0, help='Show individual benchmark results')
    argp.add_argument('--csv', type=str, default='', help='Output result in CSV format in the specified file')
    argp.add_argument('benchmarks', type=str, nargs='+', help='*.pomc files or directories containing them')
    args = argp.parse_args()

    print('Running benchmarks...')
    results = exec_all(expand_files(args.benchmarks), args)
    pretty_print(results, args.csv)
