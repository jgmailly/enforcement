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
