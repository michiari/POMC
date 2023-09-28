#!/usr/bin/env python3

from enum import Enum
import random

class Prec(Enum):
    YIELD = 0
    EQUAL = 1
    TAKE = 2

mcall = {
    ("call", "call"): Prec.YIELD,
    ("call", "ret"): Prec.EQUAL,
    ("call", "han"): Prec.YIELD,
    ("call", "exc"): Prec.TAKE,
    ("call", "stm"): Prec.YIELD,
    ("ret",  "call"): Prec.TAKE,
    ("ret",  "ret"): Prec.TAKE,
    ("ret",  "han"): Prec.TAKE,
    ("ret",  "exc"): Prec.TAKE,
    ("ret",  "stm"): Prec.TAKE,
    ("han",  "call"): Prec.YIELD,
    ("han",  "ret"): Prec.TAKE,
    ("han",  "han"): Prec.YIELD,
    ("han",  "exc"): Prec.EQUAL,
    ("han",  "stm"): Prec.YIELD,
    ("exc",  "call"): Prec.TAKE,
    ("exc",  "ret"): Prec.TAKE,
    ("exc",  "han"): Prec.TAKE,
    ("exc",  "exc"): Prec.TAKE,
    ("exc",  "stm"): Prec.TAKE,
    ("stm",  "call"): Prec.TAKE,
    ("stm",  "ret"): Prec.TAKE,
    ("stm",  "han"): Prec.TAKE,
    ("stm",  "exc"): Prec.TAKE,
    ("stm",  "stm"): Prec.TAKE
}

class pOPA:
    def __init__(self, opm, dpush, dshift, dpop, ini, fin, labels):
        self.opm = opm
        self.dpush = dpush
        self.dshift = dshift
        self.dpop = dpop
        self.ini = ini
        self.fin = fin
        self.labels = labels
        self.init()

    def init(self):
        initial, weights = self.ini
        state = random.choices(initial, weights=weights)
        self.config = (state[0], [])

    def next_move(self, config=None):
        if config:
            state, stack = config
        else:
            state, stack = self.config
        l = self.labels[state]
        if stack:
            (sl, sstate) = stack[-1]
            pr = self.opm[(sl, l)]
        else:
            pr = Prec.YIELD

        if pr == Prec.YIELD:
            next_state = pOPA.sample_move(self.dpush, state)
            stack.append((l, state))
        elif pr == Prec.EQUAL:
            next_state = pOPA.sample_move(self.dshift, state)
            stack.pop()
            stack.append((l, sstate))
        else:
            next_state = pOPA.sample_move(self.dpop, (state, sstate))
            stack.pop()

        if config:
            return next_state, stack
        else:
            self.config = (next_state, stack)

    def is_final(self, config=None):
        if config:
            state, stack = config
        else:
            state, stack = self.config
        # print(state, stack, state in self.fin and not stack)
        return state in self.fin and not stack

    def sample_move(delta, key):
        (moves, weights) = delta[key]
        return random.choices(moves, weights=weights)[0]


if __name__ == "__main__":
    simple_rec = pOPA(
        mcall,
        { 0: ([0, 1], [0.5, 0.5]) },
        { 1: ([1], [1]) },
        { (1, 0): ([1], [1]) },
        ([0], [1]),
        [1],
        { 0: "call", 1: "ret" }
    )

    rw1d = pOPA(
        mcall,
        { 0: ([0, 1], [0.5, 0.5]) },
        { 1: ([0, 1], [0.5, 0.5]) },
        { (0, 0): ([0], [1]), (1, 0): ([1], [1]) },
        ([0], [1]),
        [0, 1],
        { 0: "call", 1: "ret" }
    )

    rw1d_unbalanced = pOPA(
        mcall,
        { 0: ([0, 1], [0.6, 0.4]) },
        { 1: ([0, 1], [0.6, 0.4]) },
        { (0, 0): ([0], [1]), (1, 0): ([1], [1]) },
        ([0], [1]),
        [0, 1],
        { 0: "call", 1: "ret" }
    )

    opa = rw1d_unbalanced
    max_len = 100000
    num_samples = 10000
    term_runs = 0
    for _ in range(num_samples):
        for _ in range(max_len):
            opa.next_move()
            if opa.is_final():
                break

        if opa.is_final():
            term_runs += 1
        opa.init()

    term_prob = term_runs / num_samples
    print(term_prob)
