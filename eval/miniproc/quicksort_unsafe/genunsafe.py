#! /usr/bin/env python3

import os.path as path
from os import makedirs

all_formulas = zip(map(str, range(6)), [
    "XNu (ret And main)",
    "(call And main) --> ~ (PNu exc Or XNu exc)",
    "G ((call And qs) --> ~ (PNu exc Or XNu exc))",
    "XNu sorted",
    "G ((call And qs) --> (XNu sorted))",
    "XNd (han And PNd (call And qs And XNu (exc Or sorted)))"
])

bench_template = \
'''formulas = {spec};

program:
{program}
'''

def load_prog_unsafe():
    with open('unsafe.inc', 'r') as fsafe:
        return fsafe.read()

def gen_bench(base_path, filename_template, formulas, prog_template, width, size):
    init = '\n'.join({'a[{:d}s6] = *;'.format(n) for n in range(size)})
    comp = ' && '.join({'a[{:d}s6] <= a[{:d}s6]'.format(n, n + 1) for n in range(0, size-1)}) if size > 1 else 'true'
    content = bench_template.format(spec=',\n'.join(formulas),
                                    program=prog_template.format(width=width, size=size, init=init, comp=comp))
    filepath = path.join(base_path, filename_template.format(width=width, size=size))
    with open(filepath, 'w') as outfile:
        outfile.write(content)

def gen_suite(base_path, filename_template, formulas, prog_template, width_from, width_to, size_from, size_to):
    for size in range(size_from, size_to + 1):
        spath = path.join(base_path, 'size{:d}'.format(size))
        makedirs(spath, mode=0o775, exist_ok=True)
        for width in range(width_from, width_to + 1):
            gen_bench(spath, filename_template, formulas, prog_template, width, size)

if __name__ == '__main__':
    unsafe_template = load_prog_unsafe()

    wfrom, wto = 2, 16
    sfrom, sto = 1, 5

    for fname, f in all_formulas:
        gen_suite(path.join('bench', fname), '{width:02d}.{size:d}.pomc', [f], unsafe_template, wfrom, wto, sfrom, sto)
