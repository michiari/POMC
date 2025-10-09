Using POMC
==========

Usage
-----

POMC checks MiniProc programs or OPA against LTL or POTL formulas.
POMC can be executed on an input file ``file.pomc`` as follows:

.. code-block:: sh

   stack exec -- pomc file.pomc

By default, POMC will perform infinite-word model checking. The optional
arguments ``--finite`` and ``--infinite`` can be used to control this
behavior manually. POMC uses the explicit-state engine by default. To
use the SMT engine, use the flag ``--smt=k``, where ``k`` is a positive
integer indicating the maximum length of the encoding. For the time
being, it can only be used together with ``--finite``. So for instance,
to check an input file with the SMT-based engine type:

.. code-block:: sh

   stack exec -- pomc --finite --smt=200 file.pomc

Type ``stack exec -- pomc --help`` to see all available command-line
options.


Input Format
------------

Providing input models as programs
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The main format for POMC input files consists of a list of
requirements expressed as LTL or POTL formulas, and a program in the
MiniProc language to be checked against them.  To learn more about
MiniProc and formula syntax, check out the sections on how to write
:ref:`input-programs` and :ref:`writing-requirements`.
POMC translates every MiniProc program into an OPA,
that is then checked against the supplied formulas.
This kind of input files have the following form:

::

   formulas = FORMULA [, FORMULA ...] ;
   program:
   PROGRAM


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

When invoked on it, POMC prints the following:

::

   Model Checking
   Formula: G ((("call" And "pb") And ("call" Sd ("call" And "pa")))
     --> ((PNu "exc") Or (XNu "exc")))
   Input OPA state count: 28
   Result:  True
   Elapsed time: 803.7 ms


   Total elapsed time: 803.7 ms (8.0370e-1 s)

Additionally, POMC input files may contain C++-style single-line
comments starting with ``\\``, and C-style multi-line comments enclosed
in ``/*`` and ``*/``.

External files can be included with

::

   include = "path/to/file.inc";

where the path is relative to the ``pomc`` file location.


Providing input models as OPA
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

POMC also supports checking temporal logic formulas on OPA given explicitly.
This format is only supported by the explicit-state model checking engine.
An input file in this format must be as follows:

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


Example
'''''''

Consider the example input file ``1-generic-small.pomc``, reported below:

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

First, OPM :math:`M_\mathbf{call}` from :cite:p:`ChiariMP21` is given,
which corresponds to the following:

.. math::

   \begin{array}{r | c c c c}
            & \mathbf{call}& \mathbf{ret}& \mathbf{han}& \mathbf{exc}\\
   \hline
   \mathbf{call}& \lessdot & \doteq  & \lessdot & \gtrdot \\
   \mathbf{ret}& \gtrdot  & \gtrdot & \gtrdot  & \gtrdot \\
   \mathbf{han}& \lessdot & \gtrdot & \lessdot & \doteq \\
   \mathbf{exc}& \gtrdot  & \gtrdot & \gtrdot  & \gtrdot \\
   \end{array}


The meaning of the formula::

  G ((call And pb And (T Sd (call And pa))) --> (PNu exc Or XNu exc))

or

.. math::

 \square\big((\mathbf{call}\land \mathrm{p}_B \land
 \mathit{Scall}(\top, \mathrm{p}_A))
 \implies \mathit{CallThr}(\top) \big)

is explained in the paper.

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


Benchmarks
------------

Benchmarking script
~~~~~~~~~~~~~~~~~~~

Directory ``eval`` contains the Python script ``mcbench.py``, which
may be useful to evaluate POMC input files, as it also prints a summary
of the resources used by POMC. It must be executed with a subdirectory
of ``~/path/to/POMC-sources`` as its working directory. If invoked with
no arguments, it executes POMC on all input files in the current working
directory with the infinite-word semantics and explicit-state engine.
For instance,

.. code-block:: sh

   cd ~/path/to/POMC-sources/eval
   ./mcbench.py opa-cav

evaluates all ``*.pomc`` files in directory
``~/path/to/POMC-sources/eval/opa-cav``. The script can also be invoked
with POMC files as its arguments, which are then evaluated. For example,

.. code-block:: sh

   cd ~/path/to/POMC-sources/eval/opa-cav
   ./mcbench.py 1-generic-small.pomc 2-generic-medium.pomc

executes POMC on files ``1-generic-small.pomc`` and
``2-generic-medium.pomc``.


Usage
'''''

``mcbench.py`` can be invoked with the following optional flags:

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


Benchmark Files
~~~~~~~~~~~~~~~

Directory ``eval`` contains several POMC input files
containing POTL formulas and OPA to be checked against them.
In this section we describe some of them.
These are only a few of the experiments shipped with this repository,
and this section is intended to provide a sample of them, so it will not
be updated frequently.

.. _pomc-benchs-opa-cav:

Directory ``automata/opa-cav``
''''''''''''''''''''''''''''''

This directory contains a few programs modeled as OPA, on which POMC
proves or disproves some interesting specifications.
Files are numbered from 1 to 8.
If you wish to repeat such experiments, you may run the following
commands:

.. code-block:: sh

   cd ~/path/to/POMC-sources/eval
   ./mcbench.py -f automata/opa-cav


Generic procedural programs
'''''''''''''''''''''''''''

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

Stack Inspection
''''''''''''''''

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

Exception Safety
''''''''''''''''

:cite:t:`Sutter97` is a tutorial on how to make exception-safe
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


.. _pomc-benchs-opa-more:

Directory ``automata/opa-more``
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This directory contains more experiments devised with the purpose of
testing all POTL operators, also in order to find the most critical
cases. In fact, the complexity of POTL model checking is exponential in
the length of the formula. This is of course unsurprising, since it
subsumes logics such as LTL and NWTL, whose model checking is also
exponential. Actually, model checking is feasible for many
specifications useful in practice. There are, however, some cases in
which the exponentiality of the construction becomes evident.

We checked one of the OPA representing generic procedural programs
against several formulas.
Some of them are checked very quickly, while others
require a long execution time and a very large amount of memory.
If you wish to repeat such experiments, you may run the following commands:

.. code-block:: sh

   cd ~/path/to/POMC-sources/eval
   ./mcbench.py -f opa-more/generic-larger

Of course, a machine with a high amount of RAM is needed.


Directory ``miniproc/finite``
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This directory contains a few verification tasks in which the model has
been expressed as a MiniProc program. Each file in this directory
contains multiple formulas.

``jensen.pomc``, ``stackUnsafe.pomc`` and ``stackSafe.pomc`` contain the
same tasks as those with the same name described in
:ref:`pomc-benchs-opa-cav`. This time, however, models are expressed
as MiniProc programs, and the resulting OPA contain many more states.

Other files contain simpler programs, checked against all formulas from
:ref:`pomc-benchs-opa-more`.
