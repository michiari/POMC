.. _popacheck:

Using POPACheck
===============

Usage
-----

POPACheck can be executed on an input file ``file.pomc`` as follows:

.. code-block:: sh

   stack exec popacheck -- file.pomc {args}


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

- ``--verbose`` [default: 0]. Logging level. 0 = no logging,
  1 = show info, 2 = debug mode.

Directory ``eval`` contains the Python script ``probbench.py``, which
may be useful to evaluate POPACheck input files, as it also prints a
summary of the resources used by POPACheck. It must be executed with a
subdirectory of ``~/path/to/POPACheck-sources`` as its working
directory, and either ``--print`` to print the results in the shell,
or ``--raw_csv file_name`` for saving results in .csv format in
``file_name``.

.. code-block:: sh

   cd ~/path/to/POPACheck-sources/eval
   ./probbench.py prob/established/qualitative/schelling --print

evaluates all ``*.pomc`` files in directory
``~/path/to/POPACheck-sources/eval/prob/established/qualitative/schelling``.


Input Format
------------

POPACheck input files contain probabilistic programs
in the MiniProb programming language.
Learn how to write them in the section about :ref:`miniprob-syntax`.
The structure of input files depends on the type of query
that we are asking POPACheck to solve.


Probabilistic Queries
~~~~~~~~~~~~~~~~~~~~~

A probabilistic query must be put at the beginning of a ``.pomc`` file,
before the program. Queries follow the syntax:

.. container:: center

   :math:`\texttt{probabilistic query:} \, \, q \texttt{;}`

where :math:`q` is one of the queries in the table below:

+-------------------------------+-----------------------------+----------+
| Query                         | Meaning                     | Formula? |
+===============================+=============================+==========+
| :math:`\texttt{approximate}`  | what is the program’s       | No       |
|                               | termination probability?    |          |
+-------------------------------+-----------------------------+----------+
| :math:`\texttt{qualitative}`  | Does the program satisfy    | Yes      |
|                               | formula :math:`f` almost    |          |
|                               | surely?                     |          |
+-------------------------------+-----------------------------+----------+
| :math:`\texttt{quantitative}` | What is the probability     | Yes      |
|                               | that the program satisfies  |          |
|                               | formula :math:`f`?          |          |
+-------------------------------+-----------------------------+----------+


When a formula is needed, it has to be placed on a new line with syntax:

.. container:: center

   :math:`\texttt{formula:} \, \, f \texttt{;}`

where :math:`f` follows the syntax reported in :ref:`writing-requirements`.
For technical reasons explained in :cite:p:`abs-2404-03515`,
POPACheck does not support the whole POTL logic,
but only the operators marked with a ✓ in column POTL :math:`\chi`
of the table in :ref:`writing-requirements`.
Though, POPACheck supports full LTL. To get an idea of queries, consider
inspecting different experiments in ``eval/prob/established/``, where
the same programs are verified against different queries.

Plain reachability queries are supported through the LTL
:math:`\texttt{Eventually}` operator at the moment. We plan to optimize
them in future work, as they could be encoded as termination queries.

Additionally, POPACheck supports also the query
:math:`\texttt{unfold\&export}`, which constructs a Markov Chain in
explicit
`Storm <https://www.stormchecker.org/documentation/background/languages.html>`__
format for a given program by unfolding the program’s stack. Argument
``maxDepth`` to the stack command specifies the maximum stack depth to
unfold [default: 100]. When ``maxDepth`` is reached, recursion is not
unfolded anymore, and a simple self-loop is added. Note that MiniProb
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
if :math:`P` has non zero probability of non terminating---\
nonterminating runs do not have a matching return.


Interpreting the output
-----------------------

The output of running a query is quite verbose at the moment. For
example:

.. code-block:: sh

   stack exec -- popacheck eval/prob/established/quantitative/schelling/Q03.pomc

prints

::

  Quantitative Probabilistic Model Checking
  Query: G (((call And alice) And [| (p == [4]4)]) --> (~ (XNu obs)))
  Result:
    Lower bound: 0.8947
    Upper bound: 0.8947

  Total elapsed time: 21.06 s (2.1061e1 s)

POPACheck outputs a lower and an upper bound to the probability
that the Schelling model satisfies formula Q03.

When given the flag ``--stats``, POPACheck yields a more verbose output::

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

Most of lines just print statistics about the experiment.
The important line is::

   Floating Point Result:  (0.8947284930518479,0.894729178800233)

which shows, respectively, a lower and an upper bound to the probability
that the model satisfies the formula.
It might be of general interest to inspect the overall number of equations solved
(i.e., the size of the PPS), ``893036`` in this case, or the number of states in
the input model, ``311``.
