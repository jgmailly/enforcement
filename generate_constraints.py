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
argparser.add_argument("-ca", "--const_atts", help="the ratio of attacks that should remain (default: 0.9)", default="0.9")
argparser.add_argument("-cna", "--const_non_atts", help="the ratio of non-attacks that should remain (default: 0.9)", default="0.9")
cli_args = argparser.parse_args()

args,atts = parse(cli_args.af_file)

const_atts = []
const_non_atts = []

for attacker in args:
    for target in args:
        if [attacker, target] in atts:
            if random.random() < float(cli_args.const_atts):
                const_atts.append([attacker,target])
        else:
            if random.random() < float(cli_args.const_non_atts):
                const_non_atts.append([attacker,target])

if cli_args.verbose:
    print(f"const_atts = {const_atts}")
    print(f"const_non_atts = {const_non_atts}")

for att in const_atts:
    print(f"att({att[0]},{att[1]}).")

for non_att in const_non_atts:
    print(f"-att({non_att[0]},{non_att[1]}).")
