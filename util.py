import sys

def is_credulously_accepted(argument, initial_extensions):
    for extension in initial_extensions:
        if argument in extension:
            return True
    return False

def is_skeptically_accepted(argument, initial_extensions):
    for extension in initial_extensions:
        if argument not in extension:
            return False
    return True

def parse_target_line(query_line):
    arguments_names = query_line[7:-2]
    return arguments_names.split(",")
    
def parse_neg_target_line(query_line) :
    arguments_names = query_line[11:-2]
    return arguments_names.split(",")
    
def parse_pos_conjunct_line(query_line):
    arguments_names = query_line[13:-2]
    return arguments_names.split(",")
    
def parse_neg_conjunct_line(query_line):
    arguments_names = query_line[13:-2]
    return arguments_names.split(",")

def parse_query_file(query_file):
    with open(query_file) as query:
        query_lines = query.read().splitlines()

    target = []
    neg_target = []
    conjunctive_positive = []
    conjunctive_negative = []

    for query_line in query_lines:
        if query_line[-2:] != ").":
            sys.exit(f"Line cannot be parser in query file ({query_line})")
        
        if query_line[0:6] == "target":
            if len(target) > 0:
                sys.exit(f"The query file {query_file} should not contain more than one target line.")
            else:
                target = parse_target_line(query_line)
        elif query_line[0:10] == "neg_target":
            if len(neg_target) > 0 :
                sys.exit(f"The query file {query_file} should not contain more than one neg_target line.")
            else:
                neg_target = parse_neg_target_line(query_line)
        elif query_line[0:12] == "pos_conjunct":
            conjunctive_positive.append(parse_pos_conjunct_line(query_line))
        elif query_line[0:12] == "neg_conjunct":
            conjunctive_negative.append(parse_neg_conjunct_line(query_line))
        else:
            sys.exit(f"Line cannot be parser in query file ({query_line})")

    return target, neg_target, conjunctive_positive, conjunctive_negative


# Returns the names of the arguments in a given attack
# identified in an apx line
def parse_attack(apx_line):
    arg_names = apx_line[4:-2]
    return arg_names.split(",")

# Returns the names of the arguments in a given non-attack
# identified in an apx line
def parse_non_attack(apx_line):
    arg_names = apx_line[5:-2]
    return arg_names.split(",")

def empty_line(apx_line):
    return apx_line.strip() == ""

## Parses constraints file, i.e. apx file describing attacks and non-atttacks
## att(x,y). there is an attack from x to y
## -att(x,y). there is no attack from x to y
def parse_constraints_file(constraints_file):
    with open(constraints_file) as apxfile:
        apx_lines = apxfile.read().splitlines()

    atts = []
    non_atts = []
    for apx_line in apx_lines:
        if apx_line[0:4] == "-att":
            non_atts.append(parse_non_attack(apx_line))
        elif apx_line[0:3] == "att":
            atts.append(parse_attack(apx_line))
        elif not empty_line(apx_line):
            sys.exit(f"Line cannot be parsed ({apx_line})")

    return atts, non_atts
