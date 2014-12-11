# Fixalgs

This is a work-in-progress library that is meant to enable writing code
for different data structures that have the same shape. For example,
there are many times that one wants a binary tree structure, but the
actual data in the tree might differ. It does this by using the structure
of an F-algebra or F-coalgebra, which can be thought of as "smart constructors"
and "smart pattern matchers." In addition, it defines common transformations
on so-called unfixed data structures, such as annotating each node with a
derived value.
