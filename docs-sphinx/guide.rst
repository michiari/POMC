==================
OPPAS User’s Guide
==================

.. role:: raw-latex(raw)
   :format: latex
..

Introduction
============

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
:math:`\varphi` and an input OPA modeling some system, POMC builds the
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

We show how to use POMC and POPACheck in
Section `2 <#sec:quick-start>`__. If you wish to examine the input
formulas and OPA for the experiments more carefully, or to write your
own, we describe the format of POMC and POPACheck input files in
Sections `3 <#sec:format>`__, `4.2 <#sec:queries>`__,
and `4.3 <#sec:output>`__. Finally, Section `6 <#sec:sources>`__
contains a high-level description of the source code.

.. _`sec:quick-start`:

Quick-Start Guide
=================

OPPAS has been developed in the Haskell programming language, and
packaged with the Haskell Tool Stack [1]_.

POPACheck has a few dependencies:

- `Z3 <https://microsoft.github.io/z3guide/z3>`__ for solving
  (nonlinear) equations systems.

- `BLAS/LAPACK <https://www.netlib.org/lapack/>`__,
  `GSL <ttps://www.gnu.org/software/gsl/>`__ and
  `GLPK <https://www.gnu.org/software/glpk/>`__ for approximating
  solutions to PPSs via iterative fixpoint numerical methods (Newton’s
  method), which are used in the Haskell
  `hmatrix <https://hackage.haskell.org/package/hmatrix>`__ package.

On a Debian-based GNU/Linux distribution, they can be installed by
running:

::

   sudo apt install libz3-dev libgsl0-dev liblapack-dev libatlas-base-dev

`This
link <https://github.com/haskell-numerics/hmatrix/blob/master/INSTALL.md>`__
contains some information on how to install hmatrix dependencies on
other systems. Haskell bindings to Z3 are hosted on the GitHub
repository `haskell-z3 <https://github.com/michiari/haskell-z3>`__.

The Z3 library requires special care, because some features used by
POPACheck are buggy in older versions. The current version of the tool
(3.1.0) has been fully tested with Z3 versions 4.11.2, 4.13.4 and 4.14.1
on Ubuntu 24.10 and 25.04. We experienced some issues on with other
versions of Z3 (e.g., 4.8.12), where Z3 sometimes returns error
``Z3: invalid argument``. Please report to the OPPAS development team in
case you experience issues.

After having resolved the dependencies, the OPPAS suite can be built
from sources by typing the following commands in a shell:

::

   $ cd ~/path/to/POPACheck-sources
   $ stack setup
   $ stack build

This command automatically clones and builds also the bindings from
`haskell-z3 <https://github.com/michiari/haskell-z3>`__.

.. _pomc-1:

POMC
----

POMC can be executed on an input file ``file.pomc`` as follows:

::

   $ stack exec -- pomc file.pomc

By default, POMC will perform infinite-word model checking. The optional
arguments ``--finite`` and ``--infinite`` can be used to control this
behavior manually. POMC uses the explicit-state engine by default. To
use the SMT engine, use the flag ``--smt=k``, where ``k`` is a positive
integer indicating the maximum length of the encoding. For the time
being, it can only be used together with ``--finite``. So for instance,
to check an input file with the SMT-based engine type:

::

   $ stack exec -- pomc --finite --smt=200 file.pomc

Type ``stack exec -- pomc --help`` to see all available command-line
options.

Directory ``eval`` contains several POMC input files. Such files contain
POTL formulas and OPA to be checked against them. For more details on
the format of POMC input files, see Section `3 <#sec:format>`__.

Directory ``eval`` also contains the Python script ``mcbench.py``, which
may be useful to evaluate POMC input files, as it also prints a summary
of the resources used by POMC. It must be executed with a subdirectory
of ``~/path/to/POMC-sources`` as its working directory. If invoked with
no arguments, it executes POMC on all input files in the current working
directory with the infinite-word semantics and explicit-state engine.
E.g.,

::

   $ cd ~/path/to/POMC-sources/eval
   $ ./mcbench.py opa-cav

evaluates all ``*.pomc`` files in directory
``~/path/to/POMC-sources/eval/opa-cav``. The script can also be invoked
with POMC files as its arguments, which are then evaluated. E.g.,

::

   $ cd ~/path/to/POMC-sources/eval/opa-cav
   $ ./mcbench.py 1-generic-small.pomc 2-generic-medium.pomc

executes POMC on files ``1-generic-small.pomc`` and
``2-generic-medium.pomc``. ``mcbench.py`` can be invoked with the
following optional flags:

``-s, --smt <#k>``
   Use the SMT engine with the given value of ``k``

``-f, --finite``
   Only check finite execution traces (infinite-word model checking is
   the default)

``-i, --iters <#iters>``
   Number of iterations of the benchmarks to be performed. The final
   table printed by the script contains the mean time and memory values
   computed on all iterations. (Default: 1)

``-j, --jobs <#jobs>``
   Number of benchmarks to be run in parallel. If you provide a value
   greater than 1, make sure you have enough CPU cores on your machine.
   (Default: 1)

``-t, --timeout <timeout>``
   Timeout for benchmarks in seconds

``-M, --max-mem <limit>``
   Memory limit for benchmark in MiB

``-m, --ms``
   Output time in milliseconds instead of seconds.

``--csv <file>``
   Write results in CSV format in the given file

``-v, --verbose <level>``
   Verbosity level can be 0 (no additional info), 1 (print POMC output,
   e.g. counterexamples), or 2 (print POMC output and time/memory
   statistics).

.. _popacheck-1:

POPACheck
---------

POPACheck can be executed on an input file ``file.pomc`` as follows:

::

   $ stack exec popacheck -- file.pomc {args}

POPACheck stack commands take a few arguments:

- ``--noovi`` [default: False]. When set, POPACheck uses Z3 instead of
  OVI for computing upper bounds to termination probabilities. As the
  experimental evaluation of :cite:p:`POPACheck` suggests,
  this leads almost always to timeouts, and will probably will be
  removed in then near future.

- ``--gauss`` [default: False]. When set, POPACheck uses Value Iteration
  with Gauss-Seidel update for computing lower bounds to termination
  probabilities, and to fractions in quantitative model checking. The
  default method is Newton’s iterative method. We refer to PreMo
  publications :cite:p:`WojtczakE07,Wojtczak09` for a detailed
  description of these two numerical methods. In our experiments,
  Newton’s method tends to be slightly faster than Gauss-Seidel Value
  Iteration.

- :math:`\texttt{-verbose}` [default: 0]. Logging level. 0 = no logging,
  1 = show info, 2 = debug mode.

| Directory ``eval`` contains the Python script ``probbench.py``, which
  may be useful to evaluate POPACheck input files, as it also prints a
  summary of the resources used by POPACheck. It must be executed with a
  subdirectory of ``~/path/to/POPACheck-sources`` as its working
  directory, and either ``--print`` to print the results in the shell,
  or
| ``--raw_csv file_name`` for saving results in .csv format in
  ``file_name``.

::

   $ cd ~/path/to/POPACheck-sources/eval
   $ ./probbench.py prob/established/qualitative/schelling --print

| evaluates all ``*.pomc`` files in directory
| ``~/path/to/POPACheck-sources/eval/prob/established/qualitative/schelling``.

.. _`sec:format`:

POMC Input/Output Format
========================

.. container:: float
   :name: fig:opms

   .. container:: float
      :name: fig:mcall

      .. math::

         \begin{array}{r | c c c c}
                  & \mathbf{call}& \mathbf{ret}& \mathbf{han}& \mathbf{exc}\\
         \hline
         \mathbf{call}& \lessdot & \doteq  & \lessdot & \gtrdot \\
         \mathbf{ret}& \gtrdot  & \gtrdot & \gtrdot  & \gtrdot \\
         \mathbf{han}& \lessdot & \gtrdot & \lessdot & \doteq \\
         \mathbf{exc}& \gtrdot  & \gtrdot & \gtrdot  & \gtrdot \\
         \end{array}

   .. container:: float
      :name: fig:mstm

      .. math::

         \begin{array}{r | c c c c c}
                  & \mathbf{call}& \mathbf{ret}& \mathbf{han}& \mathbf{exc}& \mathbf{stm}\\
         \hline
         \mathbf{call}& \lessdot & \doteq  & \lessdot & \gtrdot & \lessdot \\
         \mathbf{ret}& \gtrdot  & \gtrdot & \gtrdot  & \gtrdot & \gtrdot \\
         \mathbf{han}& \lessdot & \gtrdot & \lessdot & \doteq  & \lessdot \\
         \mathbf{exc}& \gtrdot  & \gtrdot & \gtrdot  & \gtrdot & \gtrdot \\
         \mathbf{stm}& \gtrdot  & \gtrdot & \gtrdot  & \gtrdot & \gtrdot \\
         \end{array}

POMC takes in input plain text files of two possible formats.

Providing input models as OPA
-----------------------------

The first input format contains a requirement specification in terms of
a list of POTL formulas, and an OPA to be checked against them. This
format is only supported by the explicit-state engine. An input file
must be as follows:

::

   formulas = FORMULA [, FORMULA ...] ;
   prec = SL PR SL [, SL PR SL ...] ;
   opa:
     initials = STATE_SET ;
     finals = STATE_SET ;
     deltaPush = (STATE, AP_SET, STATE_SET)
                   [, (STATE, AP_SET, STATE_SET) ...] ;
     deltaShift = (STATE, AP_SET, STATE_SET)
                   [, (STATE, AP_SET, STATE_SET) ...] ;
     deltaPop = (STATE, STATE, STATE_SET)
                   [, (STATE, STATE, STATE_SET) ...] ;

where ``STATE_SET`` is either a single state, or a space-separated list
of states, surrounded by parentheses. States are non-negative integer
numbers (e.g. ``(0 1 ...)``). ``AP_SET`` is a space-separated list of
atomic propositions, surrounded by parentheses (e.g. ``(call p1)`` or
``("call" "p1")``). In more detail:

- ``prec`` is followed by a comma-separated list of precedence relations
  between structural labels, that make up an Operator Precedence Matrix.
  The list is terminated by a semicolon. Precedence relations (``PR``)
  can be one of ``<``, ``=``, or ``>``, which respectively mean
  :math:`\lessdot`, :math:`\doteq`, and :math:`\gtrdot`. Structural
  labels (``SL``) can be any sequence of alphabetic characters.

- ``formulas`` is followed by a comma-separated, semicolon-terminated
  list of POTL formulas. The syntax of such formulas is defined later in
  this section.

- ``opa`` is followed by the explicit description of an OPA or an
  :math:`\omega`\ OPBA. The list of initial and final states must be
  given, as well as the transition relations. Whether the given
  automaton is to be interpreted as an OPA or :math:`\omega`\ OPBA is
  decided by the ``--finite`` and ``--infinite`` command-line arguments.

Additionally, POMC input files may contain C++-style single-line
comments starting with ``\\``, and C-style multi-line comments enclosed
in ``/*`` and ``*/``.

External files can be included with

::

   include = "path/to/file.inc";

where the path is relative to the ``pomc`` file location.

POTL formulas can be written by using the operators in the “POMC
Operator” column of Table `1 <#tab:potl-syntax>`__, following the same
syntax rules as in :cite:p:`ChiariMP21`. Normal and structural
labels can be expressed as normal atomic propositions.

Once POMC is executed on an input file in the format above, it checks
whether the given OPA satisfies the given formulas, one by one.

Consider the example input file ``1-generic-small.pomc``, reported
below:

::

   prec = call < call, call = ret, call < han, call > exc,
          ret > call,  ret > ret,  ret > han,  ret > exc,
          han < call,  han > ret,  han < han,  han = exc,
          exc > call,  exc > ret,  exc > han,  exc > exc;

   formulas = G ((call And pb And (T Sd (call And pa)))
                    --> (PNu exc Or XNu exc));

   opa:
     initials = 0;
     finals = 10;
     deltaPush =
       (0, (call pa),   1),
       (1, (han),       2),
       (2, (call pb),   3),
       (3, (call pc),   4),
       (4, (call pc),   4),
       (6, (call perr), 7),
       (8, (call perr), 7);
     deltaShift =
       (4, (exc),       5),
       (7, (ret perr),  7),
       (9, (ret pa),    11);
     deltaPop =
       (4, 2, 4),
       (4, 3, 4),
       (4, 4, 4),
       (5, 1, 6),
       (7, 6, 8),
       (7, 8, 9),
       (11, 0, 10);

First, OPM :math:`M_\mathbf{call}` from :cite:p:`ChiariMP21`
(Figure `1 <#fig:mcall>`__) is chosen.

The meaning of the formula
``G ((call And pb And (T Sd (call And pa))) --> (PNu exc Or XNu exc))``,
or :math:`\square\big((\mathbf{call}\land \mathrm{p}_B \land
    \mathit{Scall}(\top, \mathrm{p}_A))
    \implies \mathit{CallThr}(\top) \big)`, is explained in the paper.

POMC will check the OPA against the formula, yielding the following
output:

::

   Model Checking
   Formula: G ((("call" And "pb") And (T Sd ("call" And "pa")))
                   --> ((PNu "exc") Or (XNu "exc")))
   Input OPA state count: 12
   Result:  True
   Elapsed time: 14.59 s


   Total elapsed time: 14.59 s (1.4593e1 s)

Indeed, the OPA does satisfy the formula. POMC also outputs the time
taken by each acceptance check and, when a formula is rejected, a
(partial) counterexample trace.

.. container::
   :name: tab:potl-syntax

   .. table:: This table contains all currently supported POTL
   operators, in descending order of precedence. Operators listed on the
   same line are synonyms. Operators in the same group have the same
   precedence. Note that operators are case sensitive.

      +-------+--------------------------------------------+----------------+----------+----------------+
      | Group | POTL Operator                              | POMC Operator  | Notation | Associativity  |
      +=======+============================================+================+==========+================+
      |       | :math:`\neg`                               | ``~``, ``Not`` | Prefix   | –              |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`\ocircle^d`                         | ``PNd``        | Prefix   | –              |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`\ocircle^u`                         | ``PNu``        | Prefix   | –              |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`\circleddash^d`                     | ``PBd``        | Prefix   | –              |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`\circleddash^u`                     | ``PBu``        | Prefix   | –              |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`\chi_F^{d}`                         | ``XNd``        | Prefix   | –              |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`\chi_F^{u}`                         | ``XNu``        | Prefix   | –              |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`\chi_P^{d}`                         | ``XBd``        | Prefix   | –              |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`\chi_P^{u}`                         | ``XBu``        | Prefix   | –              |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`\ocircle_H^{d}`                     | ``HNd``        | Prefix   | –              |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`\ocircle_H^{u}`                     | ``HNu``        | Prefix   | –              |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`\circleddash_H^{d}`                 | ``HBd``        | Prefix   | –              |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`\circleddash_H^{u}`                 | ``HBu``        | Prefix   | –              |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`\Diamond`                           | ``F``,         | Prefix   | –              |
      |       |                                            | ``Eventually`` |          |                |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`\square`                            | ``G``,         | Prefix   | –              |
      |       |                                            | ``Always``     |          |                |
      +-------+--------------------------------------------+----------------+----------+----------------+
      |       | :math:`{} \mathbin{\mathcal{U}_\chi^d} {}` | ``Ud``         | Infix    | Right          |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`{} \mathbin{\mathcal{U}_\chi^u} {}` | ``Uu``         | Infix    | Right          |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`{} \mathbin{\mathcal{S}_\chi^d} {}` | ``Sd``         | Infix    | Right          |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`{} \mathbin{\mathcal{S}_\chi^u} {}` | ``Su``         | Infix    | Right          |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`{} \mathbin{\mathcal{U}_H^d} {}`    | ``HUd``        | Infix    | Right          |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`{} \mathbin{\mathcal{U}_H^u} {}`    | ``HUu``        | Infix    | Right          |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`{} \mathbin{\mathcal{S}_H^d} {}`    | ``HSd``        | Infix    | Right          |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`{} \mathbin{\mathcal{S}_H^u} {}`    | ``HSu``        | Infix    | Right          |
      +-------+--------------------------------------------+----------------+----------+----------------+
      |       | :math:`\land`                              | ``And``,       | Infix    | Left           |
      |       |                                            | ``&&``         |          |                |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`\lor`                               | ``Or``, ``||`` | Infix    | Left           |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`\oplus`                             | ``Xor``        | Infix    | Left           |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`\implies`                           | ``Implies``,   | Infix    | Right          |
      |       |                                            | ``-->``        |          |                |
      |       +--------------------------------------------+----------------+----------+----------------+
      |       | :math:`\iff`                               | ``Iff``,       | Infix    | Right          |
      |       |                                            | ``<-->``       |          |                |
      +-------+--------------------------------------------+----------------+----------+----------------+

Providing MiniProc input models
-------------------------------

The second kind of input files also contain POTL formulas, and a program
in the *MiniProc* language to be checked against them. MiniProc is a
simplified procedural programming language, where variables are all
fixed-size (note that MiniProc is not Turing-complete, so any use of the
word ‘program’ when referring to it is a deliberate abuse of
terminology). This limitation allows POMC to translate every MiniProc
program into an OPA, that is then checked against the supplied formulas.
This kind of input files have this form:

::

   formulas = FORMULA [, FORMULA ...] ;
   program:
   PROGRAM

The syntax of MiniProc programs is reported in
Figure `4 <#fig:miniproc-syntax>`__.

.. container:: float
   :name: fig:miniproc-syntax

   ::

      PROGRAM := <DECL; ...> FUNCTION <FUNCTION ...>
      DECL := TYPE IDENTIFIER <, IDENTIFIER ...>
      TYPE := bool | uINT | sINT | uINT[INT] | sINT[INT]
      FUNCTION := IDENTIFIER (<FARG, ...>) { <DECL; ...> STMT; <STMT; ...> }
      FARG := TYPE IDENTIFIER | TYPE & IDENTIFIER
      STMT := LVALUE = BEXPR
            | LVALUE = *
            | while (GUARD) { <STMT; ...> }
            | if (GUARD) { <STMT; ...> } else { <STMT; ...> }
            | try { <STMT; ...> } catch { <STMT; ...> }
            | IDENTIFIER(<EXPR, ...>)
            | throw
      GUARD := * | EXPR
      LVALUE := IDENTIFIER | IDENTIFIER[EXPR]
      EXPR := EXPR || CONJ | CONJ
      CONJ := CONJ && BTERM | BTERM
      BTERM := IEXPR COMP IEXPR | IEXPR
      COMP := == | != | < | <= | > | >=
      IEXPR := IEXPR + PEXPR | IEXPR - PEXPR | PEXPR
      PEXPR := PEXPR * ITERM | PEXPR / ITERM | ITERM
      ITERM := !ITERM | (EXPR) | IDENTIFIER | IDENTIFIER[EXPR] | LITERAL
      LITERAL := <+|-> INTuINT | <+|-> INTsINT | true | false

In the definition, non-terminal symbols are uppercase, and keywords
lowercase. Parts surrounded by angle brackets are optional, and ellipses
mean that the enclosing group can be repeated zero or more times. An
``IDENTIFIER`` is any sequence of letters, numbers, or characters
‘``.``’, ‘``:``’ and ‘``_``’, starting with a letter or an underscore.

The program starts with a variable declaration, which must include all
global variables used in the program. Variables can be Boolean, or of
signed or unsigned fixed-width integer types, or fixed-size arrays
thereof. Then, a sequence of functions are defined, the first one being
the entry-point to the program. Functions can have formal parameters
that are passed by value or by value-result,  [2]_ the latter being
marked with the ``&`` symbol. Function bodies consist of
semicolon-separated statements, which start after zero or more lists of
local variables. Assignments, while loops and ifs have the usual
semantics. The try-catch statement executes the catch block whenever an
exception is thrown by any statement in the try block (or any function
it calls). Exceptions are thrown by the ``throw`` statement, and they
are not typed (i.e., there is no way to distinguish different kinds of
exceptions). Functions can be called by prepending their name to actual
parameters enclosed in parentheses. Actual parameters passed by
value-result can only be variable names. Expressions can be made of the
usual arithmetic operations when they involve integer variables, and
arrays can be indexed by integer expressions enclosed in square
brackets, both for assigning and reading them. Integer literals can be
specified by a decimal number followed by the type of the literal (e.g.,
``u8`` for an 8-bit unsigned integer, ``s16`` for a 16-bit signed
integer, etc.), possibly preceded by its sign. Boolean expressions can
contain comparisons between integers, and can be composed through the
logical and (``&&``), or (``||``) and negation (``!``) operators.

POMC automatically translates such programs into OPA or
:math:`\omega`\ OPBA, depending on whether finite- or infinite-word
model checking has been chosen. The way this is done is detailed in
Appendix `7 <#sec:miniproc-to-opa>`__.

It is possible to declare *modules* by including a double colon (``::``)
in function names. E.g., function ``A::B::C()`` is contained in module
``A::B``, which is contained in ``A``. In the OPA resulting from the
program, the module names hold whenever a contained function is called
or returns. This is useful for referring to multiple functions at once
in POTL formulas, hence drastically reducing formula length and closure
size.

When providing input models as programs, it is possible to use MiniProc
expressions as atomic propositions in POTL formulas by using the syntax

.. container:: center

   ``[ IDENTIFIER | EXPR ]``

where ``IDENTIFIER``, which is optional, is a function name and ``EXPR``
is any MiniProc expression as defined in
Figure `4 <#fig:miniproc-syntax>`__. The expression will be evaluated in
the scope of the specified function, or in the global scope if none is
given; it will evaluate to false during the execution of all other
functions. The expression may only refer to variables either global or
local to the specified function, and an error is raised otherwise.

An example input file is given below:

::

   formulas = G ((call And pb And (call Sd (call And pa)))
                   --> (PNu exc Or XNu exc));

   program:
   var foo;

   pa() {
     foo = false;
     try {
       pb();
     } catch {
       pc();
     }
   }

   pb() {
     if (foo) {
       throw;
     } else {}
   }

   pc() { }

POMC prints the following:

::

   Model Checking
   Formula: G ((("call" And "pb") And ("call" Sd ("call" And "pa")))
     --> ((PNu "exc") Or (XNu "exc")))
   Input OPA state count: 28
   Result:  True
   Elapsed time: 803.7 ms


   Total elapsed time: 803.7 ms (8.0370e-1 s)

POPACheck Input/Output Language
===============================

.. container:: float
   :name: fig:miniprob

   .. math::

      \begin{aligned}
      \mathit{prog} \coloneqq & \; [\mathit{decl} ; \dots] \; \mathit{func} \; [\mathit{func} \dots] \\
      \mathit{decl} \coloneqq & \; \mathit{type \; identifier} \; [, \mathit{identifier} \dots] \\
      \mathit{type} \coloneqq & \; \mathtt{bool} \mid \mathtt{u}\mathit{int} \mid \mathtt{s}\mathit{int} \mid \mathtt{u}\mathit{int}[\mathit{int}] \mid \mathtt{s}\mathit{int}[\mathit{int}] \\
      \mathit{func} \coloneqq & \; f \texttt{(}\mathit{type} \; [\&] x_1 \; [, \mathit{type} \; [\&] x_2 \dots]\texttt{)} \\
        &\; \{ [\mathit{decl} ; \dots] \; \mathit{block} \} \\
      \mathit{stmt} \coloneqq
          & \; \mathit{lval} = e \\
          &\mid \mathit{lval} = \mathtt{Distribution}\texttt{(} \dots \texttt{)} \\
          &\mid \mathit{lval} = e_1 \{ e_2 : e_3 \} [e_4 \{ e_5 : e_6 \} \dots] e_n \\
      %    &\mid f\texttt{(}e_1 \mid \mathit{lval}_1 \; [, e_2 \mid \mathit{lval}_2 \dots]\texttt{)} \\
          &\mid [\texttt{query}] \; f\texttt{(}e_1 \mid \mathit{lval}_1 \; [, e_2 \mid \mathit{lval}_2 \dots]\texttt{)} \\
          &\mid \mathtt{if} \; \texttt{(}e\texttt{)} \; \{ \mathit{block} \} \ \mathtt{else} \ \{ \mathit{block} \} \\
          &\mid \mathtt{while} \; \texttt{(}e\texttt{)} \; \{ \mathit{block} \} \\
          &\mid \mathtt{observe} \; \texttt{(}e\texttt{)} \\
      \mathit{block} \coloneqq & \; \mathit{stmt} ; [\mathit{stmt} \dots ; ] \\
      \mathit{lval} \coloneqq & \; \mathit{identifier} \mid \mathit{identifier}[e]
      \end{aligned}

POPACheck analyzes programs written in MiniProb, a simple probabilistic
programming language (Fig. `5 <#fig:miniprob>`__). MiniProb programs are
written in files with extension ``.pomc``. MiniProb supports (un)signed
integer variables of arbitrary width (``u8`` is an 8-bit unsigned type)
and fixed-size arrays. Functions take parameters by value or
value-result (with &). Actual parameters can only be variable
identifiers for value-result parameters, and any expression if passed by
value. Expressions consist of variables, array indexing, integer
constants, and the usual arithmetic and Boolean operators, including
comparisons. Boolean operators handle integers (0 means false,
everything else true). Programs may sample from
:math:`\texttt{Bernoulli(} e_1, e_2 \texttt{)}`, which returns 1 with
probability :math:`p = e_1 / e_2`, and 0 with probability :math:`1-p`,
or from :math:`\texttt{Uniform(} e_1, e_2 \texttt{)}`, which samples
uniformly among integers from :math:`e_1` to :math:`e_2 - 1`. Random
assignments of the form :math:`x = e_1 \{ e_2 / e_3 \} e_4` mean that
:math:`x` is assigned the value of :math:`e_1` with probability
:math:`e_2 / e_3`, and :math:`e_4` with probability
:math:`1 - e_2 / e_3`. Finally, functions can ``query`` the distribution
on value-result parameters of another function, and condition on a
Boolean expression with ``observe``.

Comparison with WebPPL
----------------------

For comparison, we show informally how constructs of a general purpose
probabilistic programming language, WebPPL [3]_, map to MiniProb
operators.

Sampling
~~~~~~~~

Sampling from primitive distributions is implicit in MiniProb, hence
WebPPL

::

     var a = sample(dist);

translates to MiniProb directly to

::

     s16 a;
     a = dist;

where we have assumed that variable ``a`` is a 16-bit signed integer. In
MiniProb, all variables must be declared before usage. Sampling from the
distribution obtained from marginal inference directly is not possible
in MiniProb, we show later a workaround.

Primitive Distributions
~~~~~~~~~~~~~~~~~~~~~~~

All WebPPL primitive distributions that are supported by MiniProb are
listed in the following table. Those not listed here are not supported.
Note that MiniProb supports only discrete probability distributions, and
rational probabilities.

.. container::
   :name: tab:distributions

   .. table:: Available primitive distributions in MiniProb. In WebPPL
   categorical or discrete distributions, ``ps`` are (unnormalized)
   probabilities, and ``vs`` are values for categorical ones. However,
   probabilities must be normalized in the MiniProb construct.

      +-----------------+--------------------------------------+-------------------------------------------------------------------------+
      | Distribution    | WebPPL                               | MiniProb                                                                |
      +=================+======================================+=========================================================================+
      | Bernoulli       | ``Bernoulli({p:e})``                 | ``Bernoulli(e1,e2)`` *with e = e1/e2*                                   |
      +-----------------+--------------------------------------+-------------------------------------------------------------------------+
      | Categorical     | ``Categorical({ps:...,vs:...})``     | vs[0]\ ``{``\ ps[0]\ ``}``\ vs[1]\ ``...{``\ ps[n-2]\ ``}``\ vs[n-1]    |
      +-----------------+--------------------------------------+-------------------------------------------------------------------------+
      | Coin flip       | ``flip([p])``                        | ``1{p}0``                                                               |
      +-----------------+--------------------------------------+-------------------------------------------------------------------------+
      | Delta           | ``Delta(``\ ``v:...``\ ``)``         | ``v``                                                                   |
      +-----------------+--------------------------------------+-------------------------------------------------------------------------+
      | Discrete        | ``Discrete({ps:...})``               | 0\ ``{``\ ps[0]\ ``}``\ 1\ ``{``\ ps[1]\ ``}...{``\ ps[n-2]\ ``}``\ n-1 |
      +-----------------+--------------------------------------+-------------------------------------------------------------------------+
      | Integer Uniform | ``RandomInteger(``\ ``n:...``\ ``)`` | ``Uniform(0,n-1)``                                                      |
      +-----------------+--------------------------------------+-------------------------------------------------------------------------+

Marginal Inference
~~~~~~~~~~~~~~~~~~

(Cit.) Marginal inference (or just inference) is the process of reifying
the distribution on return values implicitly represented by a stochastic
computation.

In WebPPL, it is expressed as, for example,

::

     var a = sample (Infer(function() {
       return flip() + flip();
     }));

In MiniProb, it corresponds to

::


     main() {
       u2 a;
       query function(a);
     }

     function (u2 &res) {
       bool b,c;
       b = 1{1/2}0;
       c = 1{1/2}0;
       res = b + c;
     }

In a nutshell, ``query ..`` corresponds to ``Infer(..)``. In MiniProb
procedures do not have a return statement; however it is possible to
bind a variable ``a`` to a sample from the the queried distribution by
passing ``a`` to a parameter by value-result (i.e., with &) of the
queried function, and then assigning a sample from the distribution to
the parameter as last statement of the queried function.

Conditioning
~~~~~~~~~~~~

The only conditioning construct in MiniProb is ``observe(c)``,
corresponding to ``condition(bool)`` in WebPPL.

.. _`sec:queries`:

Model Check Queries
-------------------

A model check query must be put at the beginning of a ``.pomc`` file,
before the program. It follows the syntax:

.. container:: center

   :math:`\texttt{probabilistic query:} \, \, q \texttt{;}`

where :math:`q` is one of the queries of Table `3 <#tab:queries>`__.
When a formula is needed, it has to be placed on a new line with syntax:

.. container:: center

   :math:`\texttt{formula:} \, \, f \texttt{;}`

where :math:`f` follows the syntax of Table `4 <#tab:potlf-syntax>`__.
For some technical reasons explained in
:cite:p:`abs-2404-03515`, POPACheck does not support the whole
POTL logic. In a single line, this is due to the fact that the model
check algorithm avoids determinization of the specification automata.
Though, POPACheck supports full LTL. To get an idea of queries, consider
inspecting different experiments in ``eval/prob/established/``, where
the same programs are verified against different queries.

Plain reachability queries are supported through the LTL
:math:`\texttt{Eventually}` operator at the moment. We plan to optimize
it in future work, as they could be encoded as a termination query.

Additionally, POPACheck supports also the query
:math:`\texttt{unfold\&export}`, which constructs a Markov Chain in
explicit
`Storm <https://www.stormchecker.org/documentation/background/languages.html>`__
format for a given program by unfolding the program’s stack. Argument
``maxDepth`` to the stack command specifies the maximum stack depth to
unfold [default: 100]. When ``maxDepth`` is reached, recursion is not
unfolded anymore, and a simple self-loop is added. Note that ``.pomc``
programs may have infinite recursion. We use this feature for testing
purposes, and do not advertise users to try it out.

An example: Pre/Post Conditions.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

With POTLf\ :math:`\chi` it is possible to express and check
automatically pre/post conditions on recursive programs. Consider the
following Hoare triple:

.. container:: center

   :math:`\varphi \, \, \{ \, P \, \} \,\, \theta`

where :math:`P` is a potentially recursive program. We want to check
whether, if :math:`\varphi` holds at a call of :math:`P`
(*pre-condition*), then :math:`\theta` holds at the corresponding return
(*post-condition*). This requirement cannot be expressed with LTL as it
is a context-free requirement, but it can be expressed with
POTLf\ :math:`\chi` via:

.. container:: center

   :math:`\texttt{probabilistic query: qualitative;}`
   :math:`\texttt{formula: G ((call And P And } \varphi \texttt{) Implies (XNu (ret And P And } \theta \texttt{)))}`

which means that *always* (``G)``, *if* the program is in a state
calling :math:`P` and where :math:`\varphi` holds, *then* (``Implies``)
this call has a matching return (``XNu (ret And P)``) where
:math:`\theta` holds. Note that this formula does not hold almost surely
if :math:`P` has non zero probability of non terminating -
nonterminating runs do not have a matching return.

.. container::
   :name: tab:queries

   .. table:: Available queries.

      +-------------------------------+-----------------------------+----------+
      | Query                         | Meaning                     | Formula? |
      +===============================+=============================+==========+
      | :math:`\texttt{approximate}`  | what is the program’s       | No       |
      |                               | termination probability?    |          |
      +-------------------------------+-----------------------------+----------+
      | :math:`\texttt{qualitative}`  | Does the program satisfy    | Yes      |
      |                               | :math:`f` almost surely?    |          |
      +-------------------------------+-----------------------------+----------+
      | :math:`\texttt{quantitative}` | What is the probability     | Yes      |
      |                               | that the program satisfies  |          |
      |                               | :math:`f`?                  |          |
      +-------------------------------+-----------------------------+----------+

.. container::
   :name: tab:potlf-syntax

   .. table:: All POTL and LTL operators, in descending order of
   precedence. Operators listed on the same line are synonyms. Operators
   in the same group have the same precedence. Note that operators are
   case sensitive. **Operators not in the fragment POTLf\ :math:`\chi`
   supported by POPACheck are crossed out.**

      +-------+--------------------------------------------------------+---------------------+--------------------+-------------------+
      | Group | POTL (or LTL) Operator                                 | POPACheck Operator  | Notation           | Associativity     |
      +=======+========================================================+=====================+====================+===================+
      |       | :math:`\neg`                                           | ``~``, ``Not``      | Prefix             | –                 |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | :math:`\ocircle^d`                                     | ``PNd``             | Prefix             | –                 |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | :math:`\ocircle^u`                                     | ``PNu``             | Prefix             | –                 |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | :math:`\circleddash^d`                                 | ``PBd``             | Prefix             | –                 |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | :math:`\circleddash^u`                                 | ``PBu``             | Prefix             | –                 |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | :math:`\chi_F^{d}`                                     | ``XNd``             | Prefix             | –                 |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | :math:`\chi_F^{u}`                                     | ``XNu``             | Prefix             | –                 |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | [STRIKEOUT::math:`\chi_P^{d}`]                         | [STRIKEOUT:``XBd``] | [STRIKEOUT:Prefix] | –                 |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | [STRIKEOUT::math:`\chi_P^{u}`]                         | [STRIKEOUT:``XBu``] | [STRIKEOUT:Prefix] | –                 |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | [STRIKEOUT::math:`\ocircle_H^{d}`]                     | [STRIKEOUT:``HNd``] | [STRIKEOUT:Prefix] | –                 |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | [STRIKEOUT::math:`\ocircle_H^{u}`]                     | [STRIKEOUT:``HNu``] | [STRIKEOUT:Prefix] | –                 |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | [STRIKEOUT::math:`\circleddash_H^{d}`]                 | [STRIKEOUT:``HBd``] | [STRIKEOUT:Prefix] | –                 |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | [STRIKEOUT::math:`\circleddash_H^{u}`]                 | [STRIKEOUT:``HBu``] | [STRIKEOUT:Prefix] | –                 |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | :math:`\Diamond\,` (LTL)                               | ``F``,              | Prefix             | –                 |
      |       |                                                        | ``Eventually``      |                    |                   |
      +-------+--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | :math:`\ocircle\,` (LTL)                               | ``N``               | Prefix             | –                 |
      +-------+--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | :math:`\square\,` (LTL)                                | ``G``, ``Always``   | Prefix             | –                 |
      +-------+--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | :math:`\mathcal{U} \,` (LTL)                           | ``U``               | Infix              | Right             |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | :math:`{} \mathbin{\mathcal{U}_\chi^d} {}`             | ``Ud``              | Infix              | Right             |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | :math:`{} \mathbin{\mathcal{U}_\chi^u} {}`             | ``Uu``              | Infix              | Right             |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | [STRIKEOUT::math:`{} \mathbin{\mathcal{S}_\chi^d} {}`] | [STRIKEOUT:``Sd``]  | [STRIKEOUT:Infix]  | [STRIKEOUT:Right] |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | [STRIKEOUT::math:`{} \mathbin{\mathcal{S}_\chi^u} {}`] | [STRIKEOUT:``Su``]  | [STRIKEOUT:Infix]  | [STRIKEOUT:Right] |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | [STRIKEOUT::math:`{} \mathbin{\mathcal{U}_H^d} {}`]    | [STRIKEOUT:``HUd``] | [STRIKEOUT:Infix]  | [STRIKEOUT:Right] |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | [STRIKEOUT::math:`{} \mathbin{\mathcal{U}_H^u} {}`]    | [STRIKEOUT:``HUu``] | [STRIKEOUT:Infix]  | [STRIKEOUT:Right] |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | [STRIKEOUT::math:`{} \mathbin{\mathcal{S}_H^d} {}`]    | [STRIKEOUT:``HSd``] | [STRIKEOUT:Infix]  | [STRIKEOUT:Right] |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | [STRIKEOUT::math:`{} \mathbin{\mathcal{S}_H^u} {}`]    | [STRIKEOUT:``HSu``] | [STRIKEOUT:Infix]  | [STRIKEOUT:Right] |
      +-------+--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | :math:`\land`                                          | ``And``, ``&&``     | Infix              | Left              |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | :math:`\lor`                                           | ``Or``, ``||``      | Infix              | Left              |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | :math:`\oplus`                                         | ``Xor``             | Infix              | Left              |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | :math:`\implies`                                       | ``Implies``,        | Infix              | Right             |
      |       |                                                        | ``-->``             |                    |                   |
      |       +--------------------------------------------------------+---------------------+--------------------+-------------------+
      |       | :math:`\iff`                                           | ``Iff``, ``<-->``   | Infix              | Right             |
      +-------+--------------------------------------------------------+---------------------+--------------------+-------------------+

.. _`sec:output`:

Interpreting the output
-----------------------

The output of running a query is quite verbose at the moment. For
example:

::

   $ stack exec -- popacheck prob/established/quantitative/schelling/Q03.pomc

prints

::

   Quantitative Probabilistic Model Checking
   Query: G (((call And alice) And [| (p == [4]4)]) --> (~ (XNu obs)))
   Result:  (5064173399 % 5660011320,6145 % 6868)
   Floating Point Result:  (0.8947284930518479,0.894729178800233)
   Elapsed time: 20.74 s (total), 2.3883e-2 s (upper bounds), 2.8956e-2 s (PAST certificates), 1.1778e0 s (graph analysis),1.1905e1 s 
   (upper bounds with OVI for quant MC),7.5453e-4 s (eq system for quant MC).
   Input pOPA state count: 311
   Support graph size: 682
   Equations solved for termination probabilities: 1230
   Non-trivial equations solved for termination probabilities: 266
   SCC count in the support graph: 1117
   Size of the largest SCC in the support graph: 24
   Largest number of non trivial equations in an SCC in the Support Graph: 52
   Size of graph G: 44
   Equations solved for quant mc: 893036
   Non-trivial equations solved for quant mc: 68226
   SCC count in quant mc weight computation: 336410
   Size of the largest SCC in quant mc weight computation: 144
   Largest number of non trivial equations in an SCC in quant mc weight computation: 7318

Most of lines just print statistics about the experiment. An user may
only read

::

   Floating Point Result:  (0.8947284930518479,0.894729178800233)

which are, respectively, a lower and an upper bound to the probability
that the Schelling model satisfies formula Q03. It might be of general
interest to inspect the overall number of equations solved (i.e., the
size of the PPS), ``893036`` in this case, or the number of states in
the input model, ``311``.

.. _`sec:exp`:

Some experiments with POMC
==========================

In this section we report the results of some experiments provided in
the ``eval`` directory. The experiments were executed on a laptop with a
2.2 GHz Intel processor and 15 GiB of RAM, running Ubuntu GNU/Linux
20.04. Here we only report results with the explicit-state engine.

These are only a few of the experiments shipped with this repository,
and this section is intended to provide a sample of them, so it will not
be updated frequently.

.. _`sec:exp-opa`:

Directory ``automata/opa-cav``
------------------------------

This directory contains a few programs modeled as OPA, on which POMC
proves or disproves some interesting specifications. The resources
employed by POMC on such tasks are reported in Table `5 <#tab:eval>`__.
If you wish to repeat such experiments, you may run the following
commands:

::

   $ cd ~/path/to/POMC-sources/eval
   $ ./mcbench.py -f automata/opa-cav

.. container::
   :name: tab:eval

   .. table:: Results of the evaluation.

      +-----+------------+-----------+-----------+-------------------+--------+
      |     | Benchmark  | # states  | Time (ms) | Memory (KiB)      | Result |
      |     | name       |           |           |                   |        |
      +=====+============+===========+===========+=========+=========+========+
      | 5-6 |            |           |           | Total   | MC only |        |
      +-----+------------+-----------+-----------+---------+---------+--------+
      | 1   | generic    | 12        | 867       | 70,040  | 10,166  | True   |
      |     | small      |           |           |         |         |        |
      +-----+------------+-----------+-----------+---------+---------+--------+
      | 2   | generic    | 24        | 673       | 70,064  | 4,043   | False  |
      |     | medium     |           |           |         |         |        |
      +-----+------------+-----------+-----------+---------+---------+--------+
      | 3   | generic    | 30        | 1,014     | 70,063  | 14,160  | True   |
      |     | larger     |           |           |         |         |        |
      +-----+------------+-----------+-----------+---------+---------+--------+
      | 4   | Jensen     | 42        | 305       | 70,050  | 3,154   | True   |
      +-----+------------+-----------+-----------+---------+---------+--------+
      | 5   | unsafe     | 63        | 1,493     | 109,610 | 43,177  | False  |
      |     | stack      |           |           |         |         |        |
      +-----+------------+-----------+-----------+---------+---------+--------+
      | 6   | safe stack | 77        | 637       | 70,089  | 7,234   | True   |
      +-----+------------+-----------+-----------+---------+---------+--------+
      | 7   | unsafe     | 63        | 5,286     | 383,312 | 167,654 | True   |
      |     | stack      |           |           |         |         |        |
      |     | neutrality |           |           |         |         |        |
      +-----+------------+-----------+-----------+---------+---------+--------+
      | 8   | safe stack | 77        | 840       | 70,077  | 16,773  | True   |
      |     | neutrality |           |           |         |         |        |
      +-----+------------+-----------+-----------+---------+---------+--------+

Generic procedural programs.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Formula

.. math::

   \square\big((\mathbf{call}\land \mathrm{p}_B \land
       \mathit{Scall}(\top, \mathrm{p}_A))
       \implies \mathit{CallThr}(\top) \big)

means that whenever procedure :math:`\mathrm{p}_B` is executed and at
least one instance of :math:`\mathrm{p}_A` is on the stack,
:math:`\mathrm{p}_B` is terminated by an exception. We checked it
against three OPA representing some simple procedural programs with
exceptions and recursive procedures. The formula holds on benchmarks
no. 1 and 3, but not on no. 2.

Stack Inspection.
~~~~~~~~~~~~~~~~~

:cite:p:`JensenLT99` contains an example Java program for
managing a bank account, which uses the security framework of the Java
Development Kit to enforce user permissions. The program allows the user
to check the account balance, and to withdraw money. To perform such
tasks, the invoking program must have been granted permissions
``CanPay`` and ``Debit``, respectively. We modeled such program as an
OPA (bench. 4), and proved that the program enforces such security
measures effectively by checking it against the formula

.. math::

   \square(\mathbf{call}\land \mathtt{read} \implies
     \neg ({\top} \mathbin{\mathcal{S}_\chi^d} {(\mathbf{call}\land
                            \neg \mathtt{CanPay}
                            \land \neg \mathtt{read})}))

meaning that the account balance cannot be read if some function in the
stack lacks the ``CanPay`` permission (a similar formula checks the
``Debit`` permission).

Exception Safety.
~~~~~~~~~~~~~~~~~

:cite:p:`Sutter97` is a tutorial on how to make exception-safe
generic containers in C++. It presents two implementations of a generic
stack data structure, parametric on the element type ``T``. The first
one is not exception-safe: if the constructor of ``T`` throws an
exception during a pop action, the topmost element is removed, but it is
not returned, and it is lost. This violates the strong exception safety
:cite:p:`Abrahams00` requirement that each operation is rolled
back if an exception is thrown. The second version of the data structure
instead satisfies such requirement.

While exception safety is, in general, undecidable, it is possible to
prove the stronger requirement that each modification to the data
structure is only committed once no more exceptions can be thrown. We
modeled both versions as OPA, and checked such requirement with the
following formula:

.. math::

   \square(\mathbf{exc}\implies
            \neg ((\circleddash^u\mathtt{modified} \lor
                  \chi_P^{u}\mathtt{modified})
            \land \chi_P^{u}(\mathtt{Stack::push} \lor \mathtt{Stack::pop})))

POMC successfully found a counterexample for the first implementation
(5), and proved the safety of the second one (6).

Additionally, we proved that both implementations are *exception
neutral* (7, 8), i.e. they do not block exceptions thrown by the
underlying types.

Directory ``automata/opa-more``
-------------------------------

.. container::
   :name: tab:more-exp-large

   .. table:: Results of the additional experiments on OPA “generic
   larger”.

      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+-------------------+-------+
      | Formula                                                                                                                                                                    | Time    | Memory (KiB)      | Res-  |
      +============================================================================================================================================================================+=========+=========+=========+=======+
      | 3-4                                                                                                                                                                        | (ms)    | Tot.    | MC      | ult   |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\chi_F^{d}\mathrm{p}_\mathit{Err}`                                                                                                                                  | 1.1     | 70,095  | 175     | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\ocircle^d(\ocircle^d(\mathbf{call}\land \chi_F^{u}\mathbf{exc}))`                                                                                                  | 21.0    | 70,095  | 1,290   | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\ocircle^d(\mathbf{han}\land (\chi_F^{d}(\mathbf{exc}\land \chi_P^{u}\mathbf{call})))`                                                                              | 42.2    | 70,088  | 2,297   | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\square(\mathbf{exc}\implies \chi_P^{u}\mathbf{call})`                                                                                                              | 10.7    | 70,099  | 839     | True  |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`{\top} \mathbin{\mathcal{U}_\chi^d} {\mathbf{exc}}`                                                                                                                 | 2.2     | 70,093  | 121     | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\ocircle^d(\ocircle^d({\top} \mathbin{\mathcal{U}_\chi^d} {\mathbf{exc}}))`                                                                                         | 4.3     | 70,094  | 113     | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\square((\mathbf{call}\land \mathrm{p}_A \land ({\neg \mathbf{ret}} \mathbin{\mathcal{U}_\chi^d} {\mathrm{WRx}})) \implies \chi_F^{u}\mathbf{exc})`                 | 3,257.7 | 238,833 | 102,582 | True  |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\ocircle^d(\ocircle^u\mathbf{call})`                                                                                                                                | 0.7     | 70,094  | 139     | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\ocircle^d(\ocircle^d(\ocircle^d(\circleddash^u\mathbf{call})))`                                                                                                    | 3.4     | 70,108  | 126     | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\chi_F^{d}(\ocircle^d(\circleddash^u\mathbf{call}))`                                                                                                                | 1.3     | 70,096  | 137     | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\square((\mathbf{call}\land \mathrm{p}_A \land \mathit{CallThr}(\top)) \implies \mathit{CallThr}(\mathrm{e}_B))`                                                    | 7,793.7 | 402,420 | 173,639 | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\Diamond(\ocircle_H^{d}\mathrm{p}_B)`                                                                                                                               | 2.1     | 70,097  | 114     | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\Diamond(\circleddash_H^{d}\mathrm{p}_B)`                                                                                                                           | 2.8     | 70,097  | 114     | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\Diamond(\mathrm{p}_A \land ({\mathbf{call}} \mathbin{\mathcal{U}_H^d} {\mathrm{p}_C}))`                                                                            | 594.9   | 77,806  | 29,786  | True  |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\Diamond(\mathrm{p}_C \land ({\mathbf{call}} \mathbin{\mathcal{S}_H^d} {\mathrm{p}_A}))`                                                                            | 676.6   | 96,296  | 37,949  | True  |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\square((\mathrm{p}_C \land \chi_F^{u}\mathbf{exc}) \implies ({\neg \mathrm{p}_A} \mathbin{\mathcal{S}_H^d} {\mathrm{p}_B}))`                                       | —       | —       | —       | OOM   |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\square(\mathbf{call}\land \mathrm{p}_B \implies {\neg \mathrm{p}_C} \mathbin{\mathcal{U}_H^u} {\mathrm{p}_\mathit{Err}})`                                          | 198.2   | 70,088  | 10,606  | True  |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\Diamond(\ocircle_H^{u}\mathrm{p}_\mathit{Err})`                                                                                                                    | 1.1     | 70,093  | 114     | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\Diamond(\circleddash_H^{u}\mathrm{p}_\mathit{Err})`                                                                                                                | 1.2     | 70,089  | 114     | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\Diamond(\mathrm{p}_A \land ({\mathbf{call}} \mathbin{\mathcal{U}_H^u} {\mathrm{p}_B}))`                                                                            | 10.3    | 70,105  | 115     | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\Diamond(\mathrm{p}_B \land ({\mathbf{call}} \mathbin{\mathcal{S}_H^u} {\mathrm{p}_A}))`                                                                            | 10.8    | 70,095  | 115     | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\square(\mathbf{call}\implies \chi_F^{d}\mathbf{ret})`                                                                                                              | 3.0     | 70,095  | 112     | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\square(\mathbf{call}\implies \neg \ocircle^u\mathbf{exc})`                                                                                                         | 1.9     | 70,106  | 113     | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\square(\mathbf{call}\land \mathrm{p}_A \implies \neg \mathit{CallThr}(\top))`                                                                                      | 110.7   | 70,094  | 4,937   | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\square(\mathbf{exc}\implies \neg (\circleddash^u(\mathbf{call}\land \mathrm{p}_A) \lor \chi_P^{u}(\mathbf{call}\land \mathrm{p}_A)))`                              | 28.9    | 70,095  | 112     | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\square((\mathbf{call}\land \mathrm{p}_B \land ({\mathbf{call}} \mathbin{\mathcal{S}_\chi^d} {(\mathbf{call}\land \mathrm{p}_A)})) \implies \mathit{CallThr}(\top)` | 926.1   | 70,104  | 13,310  | True  |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\square(\mathbf{han}\implies \chi_F^{u}\mathbf{ret})`                                                                                                               | 17.0    | 70,079  | 1,252   | True  |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`{\top} \mathbin{\mathcal{U}_\chi^u} {\mathbf{exc}}`                                                                                                                 | 7.7     | 70,101  | 121     | True  |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\ocircle^d(\ocircle^d({\top} \mathbin{\mathcal{U}_\chi^u} {\mathbf{exc}}))`                                                                                         | 44.6    | 70,104  | 2,376   | True  |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\ocircle^d(\ocircle^d(\ocircle^d({\top} \mathbin{\mathcal{U}_\chi^u} {\mathbf{exc}})))`                                                                             | 123.7   | 70,090  | 5,261   | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\square(\mathbf{call}\land \mathrm{p}_C \implies ({\top} \mathbin{\mathcal{U}_\chi^u} {\mathbf{exc}\land \chi_P^{d}\mathbf{han}}))`                                 | 92.9    | 70,096  | 1,346   | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`{\mathbf{call}} \mathbin{\mathcal{U}_\chi^d} {(\mathbf{ret}\land \mathrm{p}_\mathit{Err})}`                                                                         | 1.8     | 70,107  | 114     | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\chi_F^{d}(\mathbf{call}\land ({(\mathbf{call}\lor \mathbf{exc})} \mathbin{\mathcal{S}_\chi^u} {\mathrm{p}_B}))`                                                    | 10.8    | 70,086  | 117     | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+
      | :math:`\ocircle^d(\ocircle^d({(\mathbf{call}\lor \mathbf{exc})} \mathbin{\mathcal{U}_\chi^u} {\mathbf{ret}}))`                                                             | 5.3     | 70,094  | 114     | False |
      +----------------------------------------------------------------------------------------------------------------------------------------------------------------------------+---------+---------+---------+-------+

This directory contains more experiments devised with the purpose of
testing all POTL operators, also in order to find the most critical
cases. In fact, the complexity of POTL model checking is exponential in
the length of the formula. This is of course unsurprising, since it
subsumes logics such as LTL and NWTL, whose model checking is also
exponential. Actually, model checking is feasible for many
specifications useful in practice. There are, however, some cases in
which the exponentiality of the construction becomes evident.

In Table `6 <#tab:more-exp-large>`__ we show the results of model
checking numerous POTL formulas on one of the OPA representing generic
procedural programs. Some of them are checked very quickly, while others
require a long execution time and a very large amount of memory. POMC
runs out of memory on one of such formulas. We were able to run it in
367 seconds on a server with a 2.0 GHz 16-core AMD CPU and 500 GB of
RAM. If you wish to repeat such experiments, you may run the following
commands:

::

   $ cd ~/path/to/POMC-sources/eval
   $ ./mcbench.py -f opa-more/generic-larger

Of course, a machine with an appropriate amount of RAM is needed.

Directory ``miniproc/finite``
-----------------------------

This directory contains a few verification tasks in which the model has
been expressed as a MiniProc program. Each file in this directory
contains multiple formulas.

``jensen.pomc``, ``stackUnsafe.pomc`` and ``stackSafe.pomc`` contain the
same tasks as those with the same name described in
Section `5.1 <#sec:exp-opa>`__. This time, however, models are expressed
as MiniProc programs, and the resulting OPA contain many more states.

Other files contain simpler programs, checked against all formulas form
Table `6 <#tab:more-exp-large>`__.

Table `7 <#tab:exp-miniproc>`__ reports the results of such experiments.
When more than one formula is checked in a single file, the reported
result is True only if all formulas are verified, False if at least one
of them is not.

.. container::
   :name: tab:exp-miniproc

   .. table:: Results of the evaluation of ``miniproc`` files.

      ============== ======== ======== ============ ========= ======
      Benchmark name # states Time (s) Memory (KiB)           Result
      ============== ======== ======== ============ ========= ======
      4-5                              Total        MC only   
      doubleHan      22       52.96    2,091,256    869,661   False
      jensen         1236     1.97     73,712       17,339    True
      simpleExc      19       65.42    3,278,876    1,353,000 False
      simpleExcNoHan 12       37.72    1,510,524    656,422   False
      simpleIfElse   28       27.62    942,280      383,231   False
      simpleIfThen   28       30.67    1,046,584    415,648   False
      simpleWhile    16       0.09     73,768       3,251     True
      stackSafe      340      31.51    653,616      265,363   True
      stackUnsafe    162      16.48    532,736      224,573   False
      ============== ======== ======== ============ ========= ======

.. _`sec:sources`:

Source Code
===========

The POMC suite is open source. The source code is contained in directory
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

The source code of POPACheck is contained in directory ``src/Pomc/``.

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
provider of the Tasty [4]_ framework. They can be run with

::

   $ stack test

but note that some of them may take a very long time or exhaust your
memory. To learn how to execute just some of them, please consult the
``README.md`` file in the ``test`` directory.

Acknowledgements
================

We are thankful to Tobias Winkler and Prof. Joost-Pieter Katoen (RWTH
Aachen) for the fruitful discussions and for the advice on implementing
OVI.

We are grateful to Davide Bergamaschi for developing an early prototype
of this tool, and to Francesco Pontiggia for implementing the model
checking algorithms for infinite words and performance optimizations.


.. _`sec:miniproc-to-opa`:

From MiniProc to OPA
====================

A MiniProc program can be converted to an equivalent OPA or
:math:`\omega`\ OPBA. This is done in two stages: first, we build an
*extended* OPA whose transitions are labeled with Boolean expressions
and assignments; then, we convert such OPA to a normal one, ready for
model checking. Note that this construction is outdated as it does not
explain how we deal with things such as integer variables and function
arguments, but it should still give a good overview of the process.

Extended OPA
------------

Given a MiniProc program :math:`P` and the set :math:`I_P` of
identifiers in :math:`P`, we call
:math:`L_P = \mathit{BExp}_P \cup \mathit{Ass}_P` the set of labels on
:math:`P`, where :math:`\mathit{BExp}_P` and :math:`\mathit{Ass}_P` are
resp. the sets of Boolean expressions and assignments on :math:`I_P`. We
build the extended OPA

.. math:: \mathcal{A}^E_P = (\Sigma_P, \allowbreak M_\mathbf{call}, \allowbreak Q^E_P, \allowbreak \{q_0\}, \allowbreak \{q_f\}, \allowbreak \delta^E_P)

with :math:`\Sigma_P = \Sigma_\mathbf{call}\cup L_P`. :math:`Q_P` and
:math:`\delta^E_P` are built inductively on the program structure. For
each statement :math:`s` in :math:`P`, we define the set of entry
state/label pairs :math:`\mathit{En}_s \subseteq Q_P \times L_P`. Each
entry state is labeled with an element form either
:math:`\mathit{BExp}_P` or :math:`\mathit{Ass}_P`, but not both.

Functions
   For each function :math:`f` in :math:`P` we define a set of entry
   states :math:`\mathit{En}_f = \mathit{En}_s`, where :math:`s` is the
   first statement in the function’s body; we also add transitions and
   states
   :math:`q^l_f \stackrel{\mathbf{ret}\ f}{\dashrightarrow} q^r_f`, to
   which we link the last statement in :math:`f`, and
   :math:`q^t_f \stackrel{\mathbf{exc}}{\dashrightarrow} q^e_f`, which
   implements ``throw`` statements.

Function Call
   For a call :math:`s` to function :math:`f`, we add
   :math:`q_s \stackrel{\mathbf{call}\ f \ l}{\longrightarrow} q` for
   all :math:`(q, l) \in \mathit{En}_f`, and
   :math:`q^t_f \stackrel{q_s}{\Longrightarrow} q^t_{f'}`, where
   :math:`f'` is the function containing :math:`s`. Let :math:`s'` be
   the successor of :math:`s`: we add
   :math:`q^r_f \stackrel{q_s \ l}{\Longrightarrow} q` for all
   :math:`(q, l) \in \mathit{En}_s`.

Assignments
   For each assignment :math:`s` we add
   :math:`q_s \stackrel{\mathbf{stm}\ s}{\longrightarrow}{q_s}`, and set
   :math:`\mathit{En}_s = \mathit{Ex}_s = \{(q_s, \top)\}`. Let
   :math:`s'` be the successor of :math:`s`: we add
   :math:`q_s \stackrel{(q_s, l)}{\Longrightarrow} q` for all
   :math:`(q, l) \in \mathit{En}_s`.

If-then-else
   For each statement :math:`s` of the form ``if`` :math:`b_s`
   ``then {`` :math:`s_1; \dots; s_n` ``} else {``
   :math:`s_{n+1}; \dots; s_m` ``}`` we have
   :math:`\mathit{En}_s = \{(q, b_s \land l) \mid (q, l) \in \mathit{En}_{s_1}\} \cup \{(q, \neg b_s \land l) \mid (q, l) \in \mathit{En}_{s_{n+1}}\}`.

While
   For a statement :math:`s` of the form ``while`` :math:`b_s` ``{``
   :math:`s_1; \dots; s_n` ``}`` we set
   :math:`\mathit{En}_s = \{(q, b_s \land l) \mid (q, l) \in \mathit{En}_{s_1}\} \cup \{(q, \neg b_s \land l) \mid (q, l) \in \mathit{En}_{s_{n+1}}\}`,
   where :math:`s_{n+1}` is the successor of :math:`s`. Also, both
   :math:`s_{n+1}` and :math:`s` itself are considered as successors of
   :math:`s_n`, and their entry sets are merged.

Throw
   For a ``throw`` statement :math:`s` in a function :math:`f` we just
   set :math:`\mathit{En}_s = \{(q^t_f, \top)\}`.

Try-Catch
   For a statement :math:`s` in function :math:`f` of the form ``try {``
   :math:`s_1; \dots; s_n` ``} catch {`` :math:`s_{n+1}; \dots; s_m`
   ``}``, we add a new state :math:`q_s` and set
   :math:`\mathit{En}_s = \{(q_s, \top)\}`, and a push transition
   :math:`q_s \stackrel{\mathbf{han}\ l}{\longrightarrow} q` for each
   :math:`(q, l) \in \mathit{En}_{s_1}` that installs the handler. We
   first deal with the case when an exception is caught. We add pop
   transitions :math:`q^e_f \stackrel{q_s \ l}{\Longrightarrow} q` for
   each :math:`(q, l) \in \mathit{En}_{s_{n+1}}` that pop the handler
   when an exception is thrown in the try block, and pass the execution
   flow to the catch block. Then, statement :math:`s_m` is linked to the
   entry states of :math:`s'`, the first statement after :math:`s` (how
   this is done depends on what kind of statement :math:`s_m` is). For
   the case when no exception is thrown, we add a shift transition that
   simulates a dummy ``throw`` statement :math:`t` after :math:`s_n`, to
   uninstall the handler. When lowering :math:`s_n`, we consider
   :math:`t` as its next statement, add states :math:`q_t` and
   :math:`q'_t`, and set :math:`\mathit{En}_t = \{(q_t, \top)\}`. Then
   we add
   :math:`q_t \stackrel{\mathbf{exc}\ \mathit{dummy}}{\dashrightarrow} q'_t`,
   and :math:`q'_t \stackrel{q_s \ l}{\Longrightarrow} q` for all
   :math:`(q, l) \in \mathit{En}_{s'}`, which pop the handler and
   continue the execution with the first statement after :math:`s`.

Finally, if :math:`f_0` is the first function listed in the MiniProc
program, we add transitions
:math:`q_0 \stackrel{\mathbf{call}\ f_0 \ l}{\longrightarrow} q` for all
:math:`(q, l) \in \mathit{En}_{f_0}`, and
:math:`q^r_{f_0} \stackrel{q_0}{\Longrightarrow} q_f`.

From extended OPA to OPA
------------------------

We expand states of :math:`\mathcal{A}^E_P` with all possible variable
valuations, to obtain OPA

.. math:: \mathcal{A}_P = (\Sigma_\mathbf{call}\times I_P, M_\mathbf{call}, Q_P, \{q_0\} \times \{0, 1\}^{|I_P|}, \{q_f\} \times \{0, 1\}^{|I_P|}, \delta_P),

where :math:`Q_P \subseteq Q^E_P \times \{0, 1\}^{|I_P|}`. Each state is
a pair :math:`(q, v)` with :math:`q \in Q^E_P` and :math:`v` is a
bitvector representing a possible valuation of variables that hold in
:math:`q`. By :math:`v \models l` we mean that the variable valuation
:math:`v \in \{0, 1\}^{|I_P|}` satisfies Boolean expression
:math:`l \in \mathit{BExp}_P`; if
:math:`l = (x := e) \in \mathit{Ass}_P` with :math:`x \in I_P` and
:math:`e \in \mathit{BExp}_P` we mean :math:`v \models x \iff e`. By
:math:`\operatorname{vars}(v)` we denote the set of variables satisfied
by :math:`v \in \{0, 1\}^{|I_P|}`. We define
:math:`Q_P := \bigcup_{i \in \mathbb{N}} Q_P^i` inductively through the
following equations:

.. math::

   \begin{aligned}
     &Q_P^0 := \{q_0\} \times \{0, 1\}^{|I_P|} \\
     &Q_P^{n+1} := \{(q, v) \mid q' \in Q_P^n, \ (q', a \ l, q) \in \delta^E_P, \ v \models l\}
   \end{aligned}

This is implemented through a depth-first visit of
:math:`\mathcal{A}^E_P`, from which we derive

.. math::

   \begin{aligned}
     \delta_P :=
       & \{q \stackrel{a \ \operatorname{vars(v)}}{\longrightarrow} q' \mid q \stackrel{a \ l}{\longrightarrow} q' \in \delta^E_P, \ q, q' \in Q_P\} \\
       & \cup \{q \stackrel{a \ \operatorname{vars(v)}}{\dashrightarrow} q' \mid q \stackrel{a \ l}{\dashrightarrow} q' \in \delta^E_P, \ q, q' \in Q_P\} \\
       & \cup \{q \stackrel{p}{\Longrightarrow} q' \mid q \stackrel{p \ l}{\Longrightarrow} q' \in \delta^E_P, \ q, q', p \in Q_P\}
   \end{aligned}

Note that :math:`\mathcal{A}_P` has size exponential in :math:`|I_P|` in
the worst case, but not in general, since only reachable variable
assignments are considered.

.. [1]
   https://www.haskellstack.org/

.. [2]
   When a parameter is passed by value-result, the actual parameter is
   copied into the formal parameter when the function is called and,
   when the function returns, the value of the formal parameter is
   copied back into the actual parameter (which must be a variable).

.. [3]
   Docs are available at https://docs.webppl.org/en/master/sample.html.

.. [4]
   https://github.com/UnkindPartition/tasty
