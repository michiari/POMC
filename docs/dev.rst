Development Information
=======================

To learn how to :ref:`compile-from-sources`,
check out the :ref:`installation` section.


Source Code
-----------

The OPPAS suite is open source. The source code is contained in directory
``src/Pomc/``. We describe the contents of each file below.

Parse
   This directory contains the parser for input files.

Check.hs
   This file contains the data structures and functions that implement
   the translation of POTL formulas into OPA. The ``check`` and
   ``fastcheck`` functions build the OPA and check for string
   acceptance. ``makeOpa`` returns a thunk containing an un-evaluated
   OPA, which is built on-the-fly while the calling context evaluates
   the transition functions.

DoubleSet.hs
   a data structure used by the SCC-finding algorithm.

Encoding.hs
   contains a data structure that represents a set of POTL formulas as a
   bit vector. We use it to encode OPA states in a memory-efficient form
   in Check.hs.

GStack.hs
   contains a custom implementation of a LIFO stack for the
   :math:`\omega`\ OPBA emptiness algorithms.

LogUtils.hs
   contains some logging-related functions.

MaybeMap.hs
   contains another helper data structure for the emptiness algorithms.

MiniProc.hs
   contains code that translates MiniProc programs into OPA.

ModelChecker.hs
   contains the model checking launcher functions, and a data structure
   to represent the input OPA to be checked explicitly. It calls
   ``makeOpa`` to translate the negation of the specification into an
   equivalent OPA, creates a thunk representing an un-evaluated
   intersection of the two OPA, and then uses the reachability algorithm
   from Satisfiability.hs to determine emptiness.

Opa.hs
   contains an implementation of OPA, which is used to test string
   acceptance.

OpaGen.hs
   contains a simple automated OPA generator (still experimental).

Potl.hs
   defines the datatype for POTL formulas.

Prec.hs
   defines the data type for precedence relations.

Prop.hs
   defines the data type for atomic propositions.

PropConv.hs
   contains dome functions useful to change the representation of atomic
   propositions from strings to unsigned integers. This is used by other
   parts of the program to achieve better performances, as strings are
   represented as lists of char in Haskell, which is quite inefficient.

Satisfiability.hs
   contains the reachability algorithms used in the model checker to
   decide OPA emptiness. They can also be use to decide satisfiability
   of a formula.

SatUtil.hs
   contains utility data structures for the satisfiability algorithms.

SCCAlgorithm.hs
   contains the implementation of the algorithm for finding strongly
   connected components in :math:`\omega`\ OPBA employed for the
   emptiness check.

SetMap.hs
   contains another helper data structure for satisfiability.

State.hs
   contains the data type used to represent OPA states.

TimeUtils.hs
   contains functions used to measure time.

TripleHashTable.hs
   contains a hash table used in the emptiness check.

Z3Encoding.hs
   contains the SMT-based engine.

The source code of POPACheck is contained in directory ``src/Pomc/Prob``.

FixPoint.hs
   contains the data structures to represent sparse PPSs, and vectors of
   solutions (termination probabilities). Given a PPS, it keeps track of
   those equations that are not solved, and allows to obtain a lower
   bound to their Least Fixed Point solution via either the Gauss-Seidel
   method or Newton’s method.

GGraph.hs
   contains the implementation of main qualitative and quantitative
   model checking routines. It also contains some procedures for
   building the cross-product between the formula’s automaton and the
   support chain of the pOPA (what is called graph :math:`G` in
   :cite:p:`abs-2404-03515`).

GReach.hs
   contains functions for exploring edges in graph :math:`G` that
   underpin support edges in the support chain of the pOPA. For
   qualitative model checking, it offers a simple reachability algorithm
   for building these edges. For quantitative model checking, it offers
   a SCC-based algorithm for computing both lower and upper bounds to
   the fraction associated with each edge via OVI. This amounts at
   solving PPSs strictly resembling those for termination probabilities.

MiniProb.hs
   contains the implementation of the MiniProb programming language.

OVI.hs
   contains our implementation of Optimistic Value Iteration (OVI) for
   computing upper bounds to the Least Fixed Point solution of PPSs.

ProbEncoding.hs
   contains routines for generating a Bitvector encoding of formulae
   satisfied in a support edge in the cross-product graph.

ProbModelChecking.hs
   exposes all our probabilistic model checking APIs.

ProbUtils.hs
   contains various utility functions.

SupportGraph.hs
   contains a function for building the support graph of an input pOPA,
   an intermediate formalism for the computation of the support chain.

Z3Termination.hs
   contains routines for computing termination probabilities of a pOPA,
   either via OVI or via Z3, and certifying via Z3 that such
   probabilities are exactly equal to one when needed, according to the
   semialgorithm of :cite:p:`POPACheck`.


Test Suite
----------

The ``test`` directory contains regression tests based on the HUnit
provider of the `Tasty framework <https://github.com/UnkindPartition/tasty>`__.

They can be run with

.. code-block:: sh

   stack test

but note that some of them may take a very long time or exhaust your
memory. To learn how to execute just some of them, please consult the
``README.md`` file in the ``test`` directory.


Credits
-------

We are thankful to Tobias Winkler and Prof. Joost-Pieter Katoen (RWTH
Aachen) for the fruitful discussions and for the advice on implementing
OVI.

We are grateful to Davide Bergamaschi for developing an early prototype
of this tool, and to Francesco Pontiggia for implementing the model
checking algorithms for infinite words and performance optimizations.
