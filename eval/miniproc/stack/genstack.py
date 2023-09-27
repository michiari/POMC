#! /usr/bin/env python3

import os.path as path
from os import makedirs

all_formulas = [
    'G ([|modified] --> ~(XNu exc Or PNu exc))',
    'G (call And ("Stack::push" Or "Stack::pop") --> ~ (T HUd [|modified]))',
    'G ((call And ("Stack::push" Or "Stack::pop") And XNd ret) --> ~ (T Ud (han And "Stack" And (~han Ud ("T" And PNu exc)))))'
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

    wfrom = 8
    wto = 16

    gen_suite('xnext/unsafe', 'unsafe_{width:02d}.pomc', all_formulas[0:1], unsafe_template, wfrom, wto, 32)
    gen_suite('xnext/safe', 'safe_{width:02d}.pomc', all_formulas[0:1], safe_template, wfrom, wto, 32)

    gen_suite('xnext/nondet_unsafe', 'nondet_unsafe_{width:02d}.pomc', all_formulas[0:1], unsafe_template, wfrom, wto)
    gen_suite('xnext/nondet_safe', 'nondet_safe_{width:02d}.pomc', all_formulas[0:1], safe_template, wfrom, wto)

    gen_suite('huntil/unsafe', 'unsafe_{width:02d}.pomc', all_formulas[1:2], unsafe_template, wfrom, wto, 32)
    gen_suite('huntil/safe', 'safe_{width:02d}.pomc', all_formulas[1:2], safe_template, wfrom, wto, 32)

    gen_suite('huntil/nondet_unsafe', 'nondet_unsafe_{width:02d}.pomc', all_formulas[1:2], unsafe_template, wfrom, wto)
    gen_suite('huntil/nondet_safe', 'nondet_safe_{width:02d}.pomc', all_formulas[1:2], safe_template, wfrom, wto)
