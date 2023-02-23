from util import *

### Creation of the SAT solver variables
#### SAT Variables
# Assume we have the initial theory T = (A,R) with |A| = k.
# x_{a_i, E_X'} -> (i-1)*k + X
# For building the updated theory, we need:
## r_{ai,aj} -> (m*k) + (i-1)*k + j
# For each E_X', we need k variables:
##### Maybe the last ones are not useful, think about it.
## def_{bi,ai, E_X'} -> (k*m + k*k) + (i-1)*k + X

def membership_SAT_variables(argument, extension, args, nb_updated_extensions):
    # argument : argument name
    # extension : extension index between 1 and nb_udated_extensions (included)
    i = args.index(argument) + 1
    return (i-1) * nb_updated_extensions + extension

def r_SAT_variables(attacker, target, extension, args, nb_updated_extensions):
    m = nb_updated_extensions
    k = len(args)
    i = args.index(attacker) + 1
    j = args.index(target) + 1
    return (m * k) + (i-1)*k + j

def defeat_SAT_variables(attacker, target, extension, args, nb_updated_extensions):
    k = len(args)
    m = nb_updated_extensions
    i = args.index(attacker) + 1
    j = args.index(target) + 1
    X = extension
    return (k*m) + (k*k) + (X-1)*k*k + (i-1)*k + j

### Encode target
def encode_target(target,args, nb_updated_extensions, updated_extensions, DEBUG=False):
    ## Clause 1 from paper, one for each argument in the target
    clauses = []
    for argname in target:
        new_clause = []
        for X in updated_extensions:
            new_clause.append(membership_SAT_variables(argname, X, args, nb_updated_extensions))
            clauses.append(new_clause)
            if DEBUG:
                print(clauses[-1])
    return clauses

### Encode remaining credulously accepted arguments
def remaining_credulously_accepted_arguments(args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG=False):
    clauses = []
    # Clauses 2 from paper
    for argument in args:
        if is_credulously_accepted(argument, initial_extensions):
            new_clause = []
            for X in updated_extensions:
                new_clause.append(membership_SAT_variables(argument, X, args, nb_updated_extensions))
            clauses.append(new_clause)
            if DEBUG:
                print(clauses[-1])
    return clauses

### Encode strict version
def strict_version(target, args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG=False):
    # Clauses 3 from paper, only for strict
    clauses = []
    for argument in args:
        if (argument not in target) and (not is_credulously_accepted(argument, initial_extensions)):
            for X in updated_extensions:
                clauses.append([-membership_SAT_variables(argument, X, args, nb_updated_extensions)])
                if DEBUG:
                    print(clauses[-1])
    return clauses


# Clauses from Extension enforcement by Niskanen et al
def encode_conflict_freeness(args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG=False):
    ## First part: conflict-freeness
    clauses = []
    for extension in updated_extensions:
        for argument_a in args:
            for argument_b in args:
                clauses.append([-r_SAT_variables(argument_a, argument_b, extension, args, nb_updated_extensions),-membership_SAT_variables(argument_a, extension, args, nb_updated_extensions),-membership_SAT_variables(argument_b, extension, args, nb_updated_extensions)])
                if DEBUG:
                    print(clauses[-1])
    return clauses

def encode_def_variables(args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG=False):
    ## Second part: semantics of def-variables
    clauses = []
    for extension in updated_extensions:
        for argument_a in args:
            for argument_b in args:
                clauses.append([-defeat_SAT_variables(argument_b, argument_a, extension, args, nb_updated_extensions),membership_SAT_variables(argument_b, extension, args, nb_updated_extensions)])
                clauses.append([-defeat_SAT_variables(argument_b, argument_a, extension, args, nb_updated_extensions),r_SAT_variables(argument_b, argument_a, extension, args, nb_updated_extensions)])
                clauses.append([-membership_SAT_variables(argument_b, extension, args, nb_updated_extensions),-r_SAT_variables(argument_b, argument_a, extension, args, nb_updated_extensions),defeat_SAT_variables(argument_b, argument_a, extension, args, nb_updated_extensions)])
                if DEBUG:
                    print(clauses[-3:])
    return clauses

def encode_stability(args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG=False):
    ## Third part: stability
    clauses = []
    for extension in updated_extensions:
        for argument_a in args:
            new_clause = [membership_SAT_variables(argument_a, extension, args, nb_updated_extensions)]
            for argument_b in args:
                new_clause.append(defeat_SAT_variables(argument_b, argument_a, extension, args, nb_updated_extensions))
            clauses.append(new_clause)
            if DEBUG:
                print(clauses[-1])
    return clauses


### Minimal change of the graph: soft clauses (all with weight=1) corresponding to the attack relation of the initial AF
def encode_graph_minimal_change(args, atts, nb_updated_extensions, DEBUG=False):
    # r_SAT_variables(attacker, target, extension, args, nb_updated_extensions)
    clauses = []
    if DEBUG:
        print("-- Soft clauses --")
    for attacker in args:
        for target in args:
            if [attacker, target] in atts:
                clauses.append([r_SAT_variables(attacker, target, 1, args, nb_updated_extensions)])
            else:
                clauses.append([-r_SAT_variables(attacker, target, 1, args, nb_updated_extensions)])
            if DEBUG:
                print(clauses[-1])
    if DEBUG:
        print("-- End soft clauses--")
    return clauses

##### Decoding
def decode_model_as_af(model,args,nb_updated_extensions):
    result = ""
    for argument in args:
        result += f"arg({argument}).\n"
    for attacker in args:
        for target in args:
            if r_SAT_variables(attacker, target, 1, args, nb_updated_extensions) in model:
                result += f"att({attacker},{target}).\n"
    return result
