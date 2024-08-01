#! /usr/bin/env python3

import os.path as path
from os import makedirs

all_formulas = [
    ('auth_cp', 'G ((call And Not ("main" Or "P_cp")) --> Not (T Ud (call And read)))'),
    ('auth_db', 'G ((call And Not ("main" Or "P_db")) --> Not (T Ud (call And write)))'),
    ('no_auth_exc', 'G (call And (("account.canpay" And Not "P_cp") Or ("account.debit" And Not "P_db")) --> PNu exc Or XNu exc)'),
    ('neg_balance', 'Not (T Ud [|balance < 0s8])')
]

bench_template = \
'''formulas = {spec};

program:
{program}
'''

def load_prog_safe():
    with open('jensen.inc', 'r') as fsafe:
        return fsafe.read()

def gen_bench(base_path, filename_template, formulas, prog_template, width):
    initial = 2**(width - 2) - 1
    content = bench_template.format(spec=',\n'.join(formulas),
                                    program=prog_template.format(width=width, initial=initial))
    filepath = path.join(base_path, filename_template.format(width=width))
    with open(filepath, 'w') as outfile:
        outfile.write(content)

def gen_suite(base_path, filename_template, formulas, prog_template, width_from, width_to):
    makedirs(base_path, mode=0o775, exist_ok=True)
    for width in range(width_from, width_to + 1):
        gen_bench(base_path, filename_template, formulas, prog_template, width)

if __name__ == '__main__':
    safe_template = load_prog_safe()

    wfrom = 2
    wto = 16

    for fname, f in all_formulas:
        gen_suite(path.join('bench', fname), '{width:02d}.pomc', [f], safe_template, wfrom, wto)
