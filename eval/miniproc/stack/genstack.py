#! /usr/bin/env python3

import os.path as path
from os import makedirs

all_formulas = [
    ('safety_xnext', 'G ([|modified] --> ~(XNu exc Or PNu exc))'),
    ('safety_huntil', 'G (call And ("Stack::push" Or "Stack::pop") --> ~ (T HUd [|modified]))'),
    ('neutrality', 'G ((call And ("Stack::push" Or "Stack::pop") And XNd ret) --> ~ (T Ud (han And "Stack" And (~han Ud ("T" And PNu exc)))))')
]

bench_template = \
'''formulas = {spec};

program:
{program}
'''

def load_prog_safe():
    with open('safe.inc', 'r') as fsafe:
        return fsafe.read()

def load_prog_unsafe():
    with open('unsafe.inc', 'r') as funsafe:
        return funsafe.read()

def gen_bench(base_path, filename_template, formulas, prog_template, width, push_val=None):
    if push_val:
        push_str = '{:d}u{:d}'.format(push_val, width)
    else:
        push_str = '*'
    content = bench_template.format(spec=',\n'.join(formulas),
                                    program=prog_template.format(width=width, aval=push_str))
    filepath = path.join(base_path, filename_template.format(width=width))
    with open(filepath, 'w') as outfile:
        outfile.write(content)

def gen_suite(base_path, filename_template, formulas, prog_template, width_from, width_to, push_val=None):
    makedirs(base_path, mode=0o775, exist_ok=True)
    for width in range(width_from, width_to + 1):
        gen_bench(base_path, filename_template, formulas, prog_template, width, push_val)

if __name__ == '__main__':
    unsafe_template = load_prog_unsafe()
    safe_template = load_prog_safe()

    wfrom = 1
    wto = 8

    for fname, f in all_formulas:
        gen_suite(path.join('unsafe', fname), '{width:02d}.pomc', [f], unsafe_template, wfrom, wto)
        gen_suite(path.join('safe', fname), '{width:02d}.pomc', [f], unsafe_template, wfrom, wto)
