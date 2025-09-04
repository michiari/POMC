.. _input-programs:

Input Programs
==============

OPPAS tools analyze programs written in a simplified procedural programming language.
POMC's input language is called MiniProc, and POPACheck's is called MiniProb.
The two languages are mostly the same, and they differ only in that MiniProc
supports non-determinism, try-catch statements and exceptions,
while MiniProb supports sampling from discrete stochastic distributions,
nested queries, and conditioning.

These languages are not Turing-complete,
because all variables are fixed-size.
So, any use of the word "program" when referring to code written in them
is a bit of an abuse of terminology.
This limitation, however, allows POMC (resp. POPACheck) to translate every MiniProc
(resp. MiniProb) program into an OPA (resp. pOPA),
that is then checked against the user-supplied requirements.


Common syntax
-------------

.. productionlist::
   prog: (`decl` ";")+ `func`+
   decl: `type` `identifier` ("," `identifier`)*
   type: "bool" | "u"`int` | "s"`int` | "u"`int`"["`int`"]" | "s"`int`"["`int`"]"
   func: `f` "(" `type` ["&"] `x₁` ("," `type` ["&"] `x₂`)+ ")"
       : "{" (`decl` ";")+ `block` "}"
   stmt: `lval` "=" `e`
       : `f` "(" (`e₁` "|" `lval₁`) ["," (`e₂` "|" `lval₂`)]* ")"
       : "if" "(" `guard` ")" "{" `block` "}" "else" "{" `block` "}"
       : "while" "(" `guard` ")" "{" `block` "}"
   block: [`stmt` ";"]+
   lval: `identifier` | `identifier` "[" `e` "]"
   guard   : `expr`
   lvalue  : `identifier`
           : `identifier` "[" `expr` "]"

An ``identifier`` is any sequence of letters, numbers, or characters
‘``.``’, ‘``:``’ and ‘``_``’, starting with a letter or an underscore.


Syntax of Expressions
~~~~~~~~~~~~~~~~~~~~~

.. productionlist::
   expr    : `expr` "||" `conj` | `conj`
   conj    : `conj` "&&" `bterm` | `bterm`
   bterm   : `iexpr` `comp` `iexpr` | `iexpr`
   comp    : "==" | "!=" | "<" | "<=" | ">" | ">="
   iexpr   : `iexpr` "+" `pexpr` | `iexpr` "-" `pexpr` | `pexpr`
   pexpr   : `pexpr` "*" `iterm` | `pexpr` "/" `iterm` | `iterm`
   iterm   : "!" `iterm` | "(" `expr` ")" | `identifier` | `identifier` "[" `expr` "]" | `literal`
   literal : `intlit` | "+" `intlit` | "-" `intlit` | "true" | "false"
   intlit  : `int` | `int`"u"`int` | `int`"s"`int`

The program starts with a variable declaration, which must include all
global variables used in the program. Variables can be Boolean, or of
signed or unsigned fixed-width integer types, or fixed-size arrays
thereof. Then, a sequence of functions are defined, the first one being
the entry-point to the program. Functions can have formal parameters
that are passed by value or by value-result [#f1]_, the latter being
marked with the ``&`` symbol. Function bodies consist of
semicolon-separated statements, which start after zero or more lists of
local variables. Assignments, while loops and ifs have the usual
semantics. Functions can be called by prepending their name to actual
parameters enclosed in parentheses. Actual parameters passed by
value-result can only be variable names. Expressions can be made of the
usual arithmetic operations when they involve integer variables, and
arrays can be indexed by integer expressions enclosed in square
brackets, both for assigning and reading them. Integer literals can be
specified by a decimal number, optionally followed by the type of the literal
(e.g., ``u8`` for an 8-bit unsigned integer, ``s16`` for a 16-bit signed
integer, etc.), and possibly preceded by its sign. Boolean expressions can
contain comparisons between integers, and can be composed through the
logical and (``&&``), or (``||``) and negation (``!``) operators.
Boolean operators also handle integers (0 means false, everything else true).

It is possible to declare *modules* by including a double colon (``::``)
in function names. E.g., function ``A::B::C()`` is contained in module
``A::B``, which is contained in ``A``. In the OPA resulting from the
program, the module names hold whenever a contained function is called
or returns. This is useful for referring to multiple functions at once
in requirements, hence drastically reducing their length.

When providing input models as programs, it is possible to use MiniProc
expressions as atomic propositions in formulas by using the syntax::

   [ identifier | expr ]

where ``identifier``, which is optional, is a function name and ``expr``
is any MiniProc expression. The expression will be evaluated in
the scope of the specified function, or in the global scope if none is
given; it will evaluate to false during the execution of all other
functions. The expression may only refer to variables either global or
local to the specified function, and an error is raised otherwise.

OPPAS tools automatically encode programs into the appropriate kind of OPA
defined on the following OPM:

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


MiniProc Syntax
---------------

We add the following syntax rules:

.. productionlist::
   guard : "*"
   stmt  : `lval` "=" "*"
         : "try" { (`stmt` ;)+ } "catch" { (`stmt` ;)+ }
         : "throw"

MiniProc (POMC's input language) additionally supports non-determinism and exception handling.
When a variable is assigned the special value ``*``,
it will be considered as if it could take any of the values allowed by its type.
Similarly, when ``*`` appears in the guard of an if or a while statement,
it non-deterministically evaluated to both ``true`` and ``false``.

The try-catch statement executes the catch block whenever an
exception is thrown by any statement in the try block (or any function
it calls). Exceptions are thrown by the ``throw`` statement, and they
are not typed (i.e., there is no way to distinguish different kinds of
exceptions).

An example MiniProc program is given below::

  bool foo;

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


.. _miniprob-syntax:

MiniProb Syntax
---------------

We add the following syntax rules:

.. productionlist::
   stmt: `lval` "=" `Distribution` "(" "..." ")"
       : `lval` "=" `e₁` ("{" `e₂` ":" `e₃` "}" `e₄`)+
       : "query" `f` "(" (`e₁` "|" `lval₁`) ["," (`e₂` "|" `lval₂`)]* ")"
       : "observe" "(" `e` ")"

POPACheck analyzes programs written in MiniProb, a simple probabilistic
programming language.

Programs may sample from
:math:`\texttt{Bernoulli(} e_1, e_2 \texttt{)}`, which returns 1 with
probability :math:`p = e_1 / e_2`, and 0 with probability :math:`1-p`,
or from :math:`\texttt{Uniform(} e_1, e_2 \texttt{)}`, which samples
uniformly among integers from :math:`e_1` to :math:`e_2 - 1`.

Random assignments of the form :math:`x = e_1 \{ e_2 / e_3 \} e_4` mean that
:math:`x` is assigned the value of :math:`e_1` with probability
:math:`e_2 / e_3`, and :math:`e_4` with probability
:math:`1 - e_2 / e_3`.

Finally, functions can ``query`` the distribution
on value-result parameters of another function, and condition on a
Boolean expression with ``observe``.


Comparison with WebPPL
~~~~~~~~~~~~~~~~~~~~~~

For comparison, we show informally how constructs of a general purpose
probabilistic programming language, WebPPL [#f2]_, map to MiniProb
operators.

Sampling
""""""""

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
in MiniProb, but we show a workaround later.

Primitive Distributions
"""""""""""""""""""""""

All WebPPL primitive distributions that are supported by MiniProb are
listed in the following table. Those not listed here are not supported.
Note that MiniProb supports only discrete probability distributions, and
rational probabilities.

.. table:: Available primitive distributions in MiniProb. In WebPPL
  categorical or discrete distributions, ``ps`` are (unnormalized)
  probabilities, and ``vs`` are values for categorical ones. However,
  probabilities must be normalized in the MiniProb construct.

  +-----------------+--------------------------------------+-------------------------------------------------------------------------+
  | Distribution    | WebPPL                               | MiniProb                                                                |
  +=================+======================================+=========================================================================+
  | Bernoulli       | ``Bernoulli({p:e})``                 | ``Bernoulli(e1,e2)`` with e = e1/e2                                     |
  +-----------------+--------------------------------------+-------------------------------------------------------------------------+
  | Categorical     | ``Categorical({ps:...,vs:...})``     | ``vs[0] { ps[0] } vs[1] ... { ps[n-2] } vs[n-1]``                       |
  +-----------------+--------------------------------------+-------------------------------------------------------------------------+
  | Coin flip       | ``flip([p])``                        | ``1{p}0``                                                               |
  +-----------------+--------------------------------------+-------------------------------------------------------------------------+
  | Delta           | ``Delta(``\ ``v:...``\ ``)``         | ``v``                                                                   |
  +-----------------+--------------------------------------+-------------------------------------------------------------------------+
  | Discrete        | ``Discrete({ps:...})``               | ``0 { ps[0] } 1 { ps[1] } ... { ps[n-2] } n-1``                         |
  +-----------------+--------------------------------------+-------------------------------------------------------------------------+
  | Integer Uniform | ``RandomInteger(``\ ``n:...``\ ``)`` | ``Uniform(0,n-1)``                                                      |
  +-----------------+--------------------------------------+-------------------------------------------------------------------------+


Marginal Inference
""""""""""""""""""

  Marginal inference (or just inference) is the process of reifying
  the distribution on return values implicitly represented by a stochastic
  computation. [#f2]_

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
""""""""""""

The only conditioning construct in MiniProb is ``observe(c)``,
corresponding to ``condition(bool)`` in WebPPL.


.. rubric:: Footnotes

.. [#f1]
   When a parameter is passed by value-result, the actual parameter is
   copied into the formal parameter when the function is called and,
   when the function returns, the value of the formal parameter is
   copied back into the actual parameter (which must be a variable).

.. [#f2]
   Docs are available at https://docs.webppl.org/en/master/sample.html
