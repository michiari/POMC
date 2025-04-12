#!/usr/bin/env python3

import argparse
from mcbench import exec_all, expand_files, to_list
import csv

# print to csv the whole table of results (for any benchmark)
def pretty_print_raw(results, csvfile):
    key_list = ['name', 'k', 'm', 'states', 'supp_size', 'eqs', 'non_trivial_eqs', 'sccs', 'maxscc', 'maxeqs', 'g_size', 'quant_eqs', 'non_trivial_quant_eqs', 'quant_sccs', 'quant_maxscc', 'quant_maxeqs', 'ub_time', 'past_time', 'gg_time', 'quant_OVI_time', 'quant_eqs_time', 'time', 'mem_tot', 'result', 'quant_result']
    results_matrix = to_list(results, list(map(lambda k: (k,  lambda x: x), key_list)))
    header = ["Name", "Array_values_bits(K)", "Array_length(M)", "|Q_A|", "|SG|", "|f|", "|f_NT|", "#SCC", "|SCC|max", "|f(SCC)_NT|max", "|G|", "|f|(quant)", "|f_NT|(quant)", "#SCC(quant)", "|SCC|max(quant)", "|f(SCC)_NT|max(quant)", "UB Time (s)", "PAST Time (s)", "G Time (s)", "quant OVI (s)", "quant Eqs (s)", "Time (s)", "Memory (KiB)", "Holds AS", "Prob"]

    with open(csvfile, 'w', newline='') as f:
        cw = csv.writer(f)
        cw.writerow(header)
        cw.writerows(results_matrix)
    
if __name__ == '__main__':
    argp = argparse.ArgumentParser()
    argp.add_argument('-o', '--noovi', action='store_true', help='Use z3 instead of OVI to compute upper bounds')
    argp.add_argument('-n', '--newton', action='store_true', help='Use Newton method for iterating fixpoint equations')
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

    # store raw results somewhere
    if args.raw_csv:
        pretty_print_raw(results, args.raw_csv)
         