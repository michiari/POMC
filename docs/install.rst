.. _installation:

Installation
============

Binary Files
------------

The easiest way to get started with OPPAS is to use the
pre-packaged OPPAS executable files from the
`GitHub release <https://github.com/corpora-lab/OPPAS/releases/tag/v3.1.0>`__.

The instructions below will work on a GNU/Linux terminal.
If you are running Windows, you will need to install the
`Windows Subsystem for Linux (WSL) <https://learn.microsoft.com/en-us/windows/wsl/>`__.
Please follow the `installation instructions <https://learn.microsoft.com/en-us/windows/wsl/install>`__ by Microsoft.
Once WSL is installed, `setup and open a terminal. <https://learn.microsoft.com/en-us/windows/wsl/setup/environment#set-up-windows-terminal>`__

If you are using GNU/Linux, you may open a terminal and proceed directly.

First extract the files from the archive with your favorite program.
For instance, open a terminal and run

.. code-block:: sh

  mkdir oppas
  tar -xvf oppas-3.1.0-x86_64.tar.xz -C oppas

The above commands creates a new directory named :code:`oppas`, and extract the files into it.

Among the files extracted from the archive, you'll find the :code:`pomc` and :code:`popacheck` executables.
Let's do a couple of quick checks to see if they work.

First, just run

.. code-block:: sh

  ./popacheck --help

This will print something like::

  POPACheck v3.1.0

followed by the usage instructions.
The same should happen when running :code:`pomc` with the :code:`--help` flag.


.. _compile-from-sources:

Compile from Sources
--------------------

OPPAS has been developed in the Haskell programming language, and
packaged with the `Haskell Tool Stack <https://www.haskellstack.org/>`__.

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
running::

   sudo apt install libz3-dev libgsl0-dev liblapack-dev libatlas-base-dev

`This link <https://github.com/haskell-numerics/hmatrix/blob/master/INSTALL.md>`__
contains some information on how to install hmatrix dependencies on
other systems. Haskell bindings to Z3 are hosted on the GitHub
repository `haskell-z3 <https://github.com/michiari/haskell-z3>`__.

The Z3 library requires special care, because some features used by
POPACheck are buggy in older versions. The current version of the tool
(3.1.0) has been fully tested with Z3 versions 4.11.2, 4.13.4 and 4.14.1
on Ubuntu 24.10 and 25.04. We experienced some issues on with other
versions of Z3 (e.g., 4.8.12), where Z3 sometimes returns error
:code:`Z3: invalid argument`. Please report to the OPPAS development team in
case you experience issues.

After having resolved the dependencies, OPPAS can be built
from sources by typing the following commands in a shell:

.. code-block:: sh

   cd ~/path/to/oppas-sources
   stack setup
   stack build

This command automatically clones and builds also the bindings from
`haskell-z3 <https://github.com/michiari/haskell-z3>`__.

Then, you can invoke POMC and POPACheck directly from Stack::

  stack exec -- pomc --help
  stack exec -- popacheck --help

Or install them somewhere with

.. code-block:: sh

  stack install --local-bin-path /install/path
