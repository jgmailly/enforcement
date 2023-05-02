### Functions for parsing an apx file (borrowed from pygarg)

import sys
import random
import argparse


# Returns the name of a certain argument
# identified in an apx line
def parse_arg(apx_line):
    return apx_line[4:-2]


# Returns the names of the arguments in a certain attack
# identified in an apx line
def parse_att(apx_line):
    arg_names = apx_line[4:-2]
    return arg_names.split(",")

def empty_line(apx_line):
    return apx_line == ""

# Parses an apx file and returns the lists of
# certain arguments, uncertain arguments, certain attacks and uncertain attacks
def parse(filename):
    with open(filename) as apxfile:
        apx_lines = apxfile.read().splitlines()

    args = []
    atts = []
    for apx_line in apx_lines:
        if apx_line[0:3] == "arg":
            args.append(parse_arg(apx_line))
        elif apx_line[0:3] == "att":
            atts.append(parse_att(apx_line))
        elif not empty_line(apx_line):
            sys.exit(f"Line cannot be parsed ({apx_line})")

    return args, atts

argparser = argparse.ArgumentParser()
argparser.add_argument("af_file",help="the file containing the AF")
argparser.add_argument("-v", "--verbose", help="increase output verbosity", action="store_true")
argparser.add_argument("-p", "--positive", help=f"the ratio of arguments in the positive query P (default: 0.1)", default="0.1")
argparser.add_argument("-n", "--negative", help=f"the ratio of arguments in the negative query N (default: 0.1)", default="0.1")
argparser.add_argument("-cp", "--conjunctpos", help="the number of conjunctive positive queries C+ (default: 0)", default="0")
argparser.add_argument("-cn", "--conjunctneg", help="the number of conjunctive negative queries C- (default: 0)", default="0")
argparser.add_argument("-cps", "--conjunctpossize", help="the size of the conjunctive positive queries in C+ (default: 2)", default="2")
argparser.add_argument("-cns", "--conjunctnegsize", help="the size of the conjunctive negative queries in C- (default: 2)", default="2")
cli_args = argparser.parse_args()

args,atts = parse(cli_args.af_file)

p = []
n = []
cplus = []
cminus = []

p_ratio = float(cli_args.positive)
n_ratio = float(cli_args.negative)

for arg in args:
    if random.random() < p_ratio:
        p.append(arg)

for arg in args:
    if (arg not in p ) and (random.random() < n_ratio):
        n.append(arg)

nb_conjunctpos = int(cli_args.conjunctpos)
nb_conjunctneg = int(cli_args.conjunctneg)

for i in range(nb_conjunctpos):
    conjunctpos = []
    for j in range(int(cli_args.conjunctpossize)):
        index = random.randint(0, len(args)-1)
        conjunctpos.append(args[index])
    cplus.append(conjunctpos)


for i in range(nb_conjunctneg):
    conjunctneg = []
    for j in range(int(cli_args.conjunctnegsize)):
        index = random.randint(0, len(args)-1)
        conjunctneg.append(args[index])
    cminus.append(conjunctneg)

if cli_args.verbose:
    print(f"p = {p}")
    print(f"n = {n}")
    print(f"cplus = {cplus}")
    print(f"cminus = {cminus}")

if len(p) > 0:
    print("target(", end='')
    for i in range(len(p)-1):
        print(f"{p[i]},", end='')
    print(f"{p[-1]}).")

if len(n) > 0:
    print("neg_target(", end='')
    for i in range(len(n)-1):
        print(f"{n[i]},", end='')
    print(f"{n[-1]}).")

for conjunctpos in cplus:
    print("pos_conjunct(", end='')
    for i in range(len(conjunctpos)-1):
        print(f"{conjunctpos[i]},", end='')
    print(f"{conjunctpos[-1]}).")

for conjunctneg in cminus:
    print("neg_conjunct(", end='')
    for i in range(len(conjunctneg)-1):
        print(f"{conjunctneg[i]},", end='')
    print(f"{conjunctneg[-1]}).")
