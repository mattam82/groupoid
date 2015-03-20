========================================================================
Distributed under the terms of the LGPL.

To compile the development, simply run 

 # coq_makefile -f _CoqProject -o Makefile; make

In the toplevel directory, with coqc in your path. You need at least Coq
8.5beta1 to compile this code, as it makes use of universe polymorphism
and fast projections.