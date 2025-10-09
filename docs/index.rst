OPPAS
=====

Operator-Precedence Program Analysis Suite
------------------------------------------

OPPAS includes two tools: **POMC** and **POPACheck**.

*POMC* is a model checker for recursive programs.
POMC models procedural programs as pushdown automata,
and checks them against requirements expressed as
Linear Temporal Logic (LTL)
and Precedence-Oriented Temporal Logic (POTL)
formulas.

*POPACheck* is an extension of POMC towards probabilistic programs
with nested queries.
It automatically models programs as
probabilistic Operator Precedence Automata (pOPA).
It supports model checking of LTL and a fragment of POTL,
called POTLf\ :math:`\chi`.
Given a probabilistic program and a
formula in either LTL or POTLf\ :math:`\chi`, POPACheck can solve
both qualitative and quantitative model checking queries.
Additionally, it can compute (approximately) the program's termination probability.
Computing termination probabilities is a central problem in
probabilistic pushdown model checking and amounts to computing
the Least Fixed Point solution of a Positive Polynomial System (PPS).

This is a reference guide to POMC's and POPACheck's usage
and describes their architecture at a high level.


.. toctree::
   :maxdepth: 2
   :caption: Contents:

   intro
   install
   programs
   requirements
   pomc
   popacheck
   dev
   biblio
