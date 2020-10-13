#!/usr/bin/env python3

import sys
import matplotlib.pyplot as plt
from matplotlib import rc

rc('font',**{'family':'serif','serif':[],'size':12})
rc('text', usetex=True)


def make_plot(states, times, mems):
    color = 'tab:red'
    plt.figure()
    plt.plot(states, times, 'o', color=color)
    plt.xlabel(r'\# states')
    plt.ylabel('Time (s)')
    plt.grid(True)
    plt.tight_layout()
    plt.savefig('time.pdf')

    color = 'tab:blue'
    plt.figure()
    plt.plot(states, mems, 'o', color=color)
    plt.xlabel(r'\# states')
    plt.ylabel('Memory (MB)')
    plt.grid(True)
    plt.tight_layout()
    plt.savefig('mem.pdf')


def parse_data(fname):
    with open(fname, 'r') as f:
        rows = f.readlines()[2:]

    split_rows = [r.split()[1:4] for r in rows]
    states_col = [int(r[0]) for r in split_rows]
    times_col = [float(r[1]) for r in split_rows]
    mems_col = [float(r[2]) for r in split_rows]
    return (states_col, times_col, mems_col)


if len(sys.argv) < 2:
    print("Usage: ", sys.argv[0], " <DATAFILE>")
    exit(0)

fname = sys.argv[1]

make_plot(*parse_data(fname))
