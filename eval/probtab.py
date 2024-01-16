#!/usr/bin/env python3

from sys import argv
from tabulate import tabulate
import csv

def load_files(files):
    records = {}
    for f in files:
        with open(f, 'r') as csvf:
            records |= {r['name']: r for r in csv.DictReader(csvf)}
    return records

def load_data(ovi_files, z3_files):
    ovi_records = load_files(ovi_files)
    for k, r in ovi_records.items():
        tokens = k.split('/')
        r['bench'] = tokens[-2]
        r['formula'] = tokens[-1].split('.')[0]

    z3_records = load_files(z3_files)
    for r in z3_records:
        if r['result'] not in ['True', 'False']:
            ovi_records[r['name']]['z3_time'] = r['result']
        else:
            ovi_records[r['name']]['z3_time'] = r['time']
    return ovi_records

def to_list(records, key_map_list):
    return [[(mapf(r[key]) if key in r else '--') for key, mapf in key_map_list] for r in records.values()]

def pretty_print(results, latex=False):
    idf = lambda x: x ## TODO: remove idf if not used
    key_map_list = [
        ('bench', idf),
        ('states', idf),
        ('supp_size', idf),
        ('eqs', idf),
        ('sccs', idf),
        ('maxscc', idf),
        ('formula', idf),
        ('z3_time', idf),
        ('ub_time', idf),
        ('past_time', idf),
        ('time', idf),
        ('mem_tot', idf),
        ('result', idf),
    ]
    results_matrix = to_list(results, key_map_list)

    header = ["Benchmark", "|Q_A|", "|SG|", "|f|", "#SCC", "|SCC|max", "formula", "z3 Time", "OVI UB Time (s)", "OVI PAST Time (s)", f"OVI Time (s)", "Memory (KiB)", "Result"]

    print(tabulate(results_matrix, headers=header, tablefmt="latex" if latex else "plain"))


def print_help(pname):
    print(f'Usage:\n{pname} [--latex] --ovi FILE [FILE] --noovi FILE [FILE]')

if __name__ == '__main__':
    if '--ovi' not in argv or '--noovi' not in argv:
        print_help(argv[0])
        exit(0)

    if argv[1] == '--ovi':
        ovi_idx = 2
        latex = False
    else:
        ovi_idx = 3
        latex = True
        if argv[1] != '--latex':
            print_help(argv[0])
            exit(0)

    noovi_idx = argv.index('--noovi')
    ovi_files = argv[ovi_idx:noovi_idx]
    z3_files = argv[noovi_idx + 1:]

    data = load_data(ovi_files, z3_files)
    pretty_print(data, latex)
