Introduction and Context
========================

POTL
----

Precedence-Oriented Temporal
Logic (POTL) :cite:p:`ChiariMP21,ChiariMP21b` is an
established temporal logic formalism for expressing many fundamental
properties on programs with recursive procedures, such as partial and
total correctness, and Hoare-style pre/post conditions. POTL is based on
the family of Operator Precedence Languages
(OPL) :cite:p:`MP18`, a subclass of deterministic context-free
languages. POTL is strictly more expressive than LTL and other temporal
logics based on subfamilies of context-free languages, such as CaRet
:cite:p:`AlurEM04` and NWTL
:cite:p:`lmcs/AlurABEIL08`. In particular, POTL reasons on an
algebraic structure equipped with, besides the usual linear order, a
binary nesting relation between word positions, which can be one-to-one,
one-to-many, or many-to-one. Such a relation is more general than the
one found in Nested Words :cite:p:`jacm/AlurM09`, because the
latter may only be one-to-one. POTL can be applied to the specification
of several kinds of requirements on procedural programs with exceptions.

POMC
----

POMC contains two different model checking engines for POTL. The
explicit-state engine employs an automata-based model checking procedure
for POTL. This procedure consists of building an Operator Precedence
Automaton (OPA), the class of pushdown automata that identifies OPL,
accepting the language denoted by a given POTL formula. The size of the
generated automaton is exponential in the length of the formula, which
is asymptotically comparable with other linear-time temporal logic
formalisms such as LTL, CaRet, and NWTL. Given a POTL formula
:math:`\varphi` and an input OPA modeling a system, POMC builds the
OPA equivalent to :math:`\neg \varphi`, computes its intersection with
the input OPA, and checks the emptiness of the resulting OPA. Both the
OPA construction and the intersection are done on-the-fly. The
explicit-state engine has been implemented for the infinite-word case
too, using :math:`\omega`\ OPBA instead of OPA.

POMC also contains a SMT-based model checking engine for POTL formulas.
It consists of a bounded SMT encoding of a tree-shaped tableau for
POTL :cite:p:`ChiariGGP24`. The tableau is complete: is the
provided bound is sufficiently large, both truth and falseness of a
formula can be proved. For the time being, this engine only supports
finite-word model checking.

POMC also supports providing input models in MiniProc, a simple
procedural programming language with exceptions. MiniProc programs are
automatically translated into equivalent OPA. The SMT-based engine only
supports MiniProc programs as inputs.

POPACheck
---------

pOPA :cite:p:`abs-2404-03515` are a class of probabilistic
pushdown automata based on OPLs. While they do not read an input, which
would make any model checking problem undecidable, the (infinite-length)
traces of state labels collected in the paths of a given pOPA constitute
an OPL.

POPACheck exploits the fact that OPLs are closed by Boolean operations
(e.g., intersection, complementation …). Roughly speaking, POPACheck:

- takes as input a formula and a program in a custom Domain-Specific
  Language called MiniProb.

- translates the program into a (explicitly represented) pOPA.

- uses POMC modules to translate the formula into an
  :math:`\omega`\ OPBA.

- model-checks the pOPA against the :math:`\omega`\ OPBA via
  automata-based model checking, i.e., via a cross-product.

Involved technicalities arise due to the facts that:

- pOPAs are equipped with an unbounded stack, hence they are
  infinite-state models.

- we do not perform determinization of the specification
  :math:`\omega`\ OPBA, as canonical in probabilistic model checking.

We’ll skip their treatment here, and refer to
:cite:p:`abs-2404-03515`. We just mention that pOPA infinite
runs can be represented (or ‘summarized’) by a finite-state Markov Chain
called *support chain*. The support chain of a pOPA can be computed by
solving (nonlinear) Positive Polynomial Systems (PPSs) of equations for
their Least Fixed Point. Solutions to these systems are called
*termination probabilities*. Due to their nonlinearity, they cannot be
computed exactly, i.e. solutions may be irrational, and not even
expressible by radicals :cite:p:`EtessamiY09`. Our tool deals
with this issue by computing sound lower and upper rational bounds to
termination probabilities. While it computes lower bound always via
numerical methods, it offers two approaches for upper bounds: one is
purely numerical, and it is called Optimistic Value Iteration (OVI); the
other one relies on the SMT solver Z3 :cite:p:`z3`. OVI has
been introduced originally by Winkler and
Katoen :cite:p:`WinklerK23a` in the tool Pray.

Similar equation systems arise in quantitative model checking. Likewise,
POPACheck computes lower and upper bounds to the Least Fixed Point
solutions of these systems—in this case, always via OVI. This means that
for quantitative model check queries POPACheck will return a lower and
an upper bound to the satisfaction probability.
