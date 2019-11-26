# formalizing-Featherweight-X10

Featherweight X10 (FX10) is a parallel programming language that can fork tasks and then await their completion in a syntactiaclly structured manner. We defined inductive types representing the syntax of FX10 and binary relations encoding the steps-to semantics, and proved a progress theorem, which implies the absence of deadlocks.

An important thing to notice is that in this proof, we proved a stronger theorem than the original theorem in the paper. Specifically, we don't have any additional restrictions on the initial program and tree, meaning that the tree doesn't have to be derived from the program and both of the tree and the program can contain function calls that are not defined in the program; when a function being called is not defined in the program, we provide a default function body. In this situation, we are still able to prove a progress theorem, which is stronger than the original one.

> Lee, Jonathan K., and Jens Palsberg. "Featherweight X10: a core calculus for async-finish parallelism." ACM Sigplan Notices. Vol. 45. No. 5. ACM, 2010.
