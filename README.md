# This is a Python implementation of the enforcement operator with minimal change of arguments statuses.
It depends on https://github.com/jgmailly/pygarg to enumerate the extension. Updated versions of pygarg may give better performance or 
provide additional semantics.
You may also need to install PySAT, which is necessary to run pygarg: https://pysathq.github.io/installation/

## Input formats
The initial argumentation framework must be described in the classical APX format, with lines defining arguments names, followed by 
lines defining the attacks:
```bash
arg(A).
arg(B).
arg(C).
arg(D).
arg(E).
att(A,B).
att(B,A).
att(A,C).
att(B,C).
att(C,D).
att(D,E).
```
The order of the arg lines is not important, and the order of the att lines is not important either, but all att lines must appear 
after the arg lines.

The enforcement query is described in an APX-like format as well, with one line describing the positive target, one line describing 
the negative target, and lines for the positive and negative conjuncts:
```bash
target(A,E).
neg_target(D).
pos_conjunct(C,E).
neg_conjunct(B,C).
```
This query means that both A and E must be accepted (but they may belong to different extensions), D should not be accepted, C and E 
should be accepted together, and finally B and C should not be accepted together. This query file can only contain one target or one 
neg_target line, but several pos_conjunct or neg_conjunct lines are possible. The order of the lines is not important.

## Command line interface
Here is the help message of the current version:
```bash
usage: main.py [-h] [-v] [-p PROBLEM] [-fo FORMAT] af_file query_file

positional arguments:
  af_file               the file containing the initial AF
  query_file            the file containing the enforcement query

optional arguments:
  -h, --help            show this help message and exit
  -v, --verbose         increase output verbosity
  -p PROBLEM, --problem PROBLEM
                        the pair XX-YY with XX in ['V1s', 'V1ns', 'OptV1s', 'OptV1ns'] and YY in ['ST']
  -fo FORMAT, --format FORMAT
                        the format of the AF file in ['apx']
```
