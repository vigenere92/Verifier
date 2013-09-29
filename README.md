Verifier
========

Requirements
1. A C++ compiler supporting C++11. For example g++ version 4.6 or higher.
2. Z3 SMT 2.0 Solver. Also Z3 SMT solver should be installed in the bin directory so
that it can be called using "z3 -smt2 filename" from the terminal.
It can be downloaded from http://z3.codeplex.com .
3. Lemon Graph Library, it can be downloaded from http://lemon.cs.elte.hu .
4. To be able to generate pdf file for the results, pdflatex is required.


Installation
The Verifier Tool can be installed by using the following procedure.
1. Copy the verifier_result folder from the Verifier directory to your home folder.
2. Using terminal, go to the Verifier folder and execute the following commands.
$ touch NEWS README AUTHORS ChangeLog
$ autoreconf --force --install
$ ./configure
$ make
$ sudo make install


For commands and options for running the verifier please refer to the manual.
