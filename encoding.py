from util import *

### Creation of the SAT solver variables
#### SAT Variables
# Assume we have the initial theory T = (A,R) with |A| = k.
# x_{a_i, E_X'} -> (i-1)*k + X
# For building the updated theory, we need:
## r_{ai,aj} -> (m*k) + (i-1)*k + j
##### To simplify the formulas, we add a variable for each combination b_i, a_i E_X',
##### which is true if b_i attacks a_i and b_i belongs to the extension E_X'
##### Intuition: b_i defeats a_i in the extension E_X'
## def_{bi,ai, E_X'} -> (k*m + k*k) + (i-1)*k + X

       
HAS_KILLER = False

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

### We assume that the last argument in the list is the "negative target killer".
def get_negative_target_killer(args):
    return args[-1]

# Ensures that an argument which is not self-attacking in the initial theory will not become so in the updated theory
def encode_no_self_attacks(args,atts,extension, nb_updated_extensions):
    clauses = []
    for argument in args:
        if [argument,argument] not in atts:
            clauses.append([-r_SAT_variables(argument, argument, extension, args, nb_updated_extensions)])
    return clauses

####### THIS SHOULD NOT BE USED
def encode_killer_unattacked(args, nb_updated_extensions):
    killer = get_negative_target_killer(args)
    clauses = []
    for other_arg in args:
        clauses.append([-r_SAT_variables(other_arg, killer, 1, args, nb_updated_extensions)])
    return clauses

def encode_killer_does_not_attack(args, nb_updated_extensions):
    killer = get_negative_target_killer(args)
    clauses = []
    for other_arg in args:
        clauses.append([-r_SAT_variables(killer, other_arg, 1, args, nb_updated_extensions)])
    return clauses
        
### Encode POSITIVE target
def encode_target(target,args, nb_updated_extensions, updated_extensions, DEBUG=False):
    if DEBUG:
        print("-- Positive target")
    ## Clause 1 from paper, one for each argument in the target
    clauses = []
    for argname in target:
        new_clause = []
        for X in updated_extensions:
            new_clause.append(membership_SAT_variables(argname, X, args, nb_updated_extensions))
        clauses.append(new_clause)
        if DEBUG:
            print(clauses[-1])
    if DEBUG:
        print("--")
    return clauses

### Encode NEGATIVE target
def encode_negative_target(neg_target,args, nb_updated_extensions, updated_extensions, DEBUG=False):
    ## Not in the paper yet. For each argument in the negative target, and each extension, add one unit clause to say that the argument is not in the extension, and the unit clause saying that the killer argument is attacked the target
    if DEBUG:
        print("-- Negative target")
    clauses = []
    if HAS_KILLER:
        clauses += encode_killer_does_not_attack(args, nb_updated_extensions)
    for argname in neg_target:
        for X in updated_extensions:
            clauses.append([-membership_SAT_variables(argname, X, args, nb_updated_extensions)])
            if DEBUG:
                print(clauses[-1])
        if HAS_KILLER:
            killer = get_negative_target_killer(args)
            clauses.append([r_SAT_variables(argname, killer, 1, args, nb_updated_extensions)])
            if DEBUG:
                print(clauses[-1])

    ## The killer is only attacked the arguments in the negative target
    if HAS_KILLER:
        for argname in args:
            if argname not in neg_target:
                killer = get_negative_target_killer(args)
                clauses.append([-r_SAT_variables(argname, killer, 1, args, nb_updated_extensions)])
                if DEBUG:
                    print(clauses[-1])

    ## The killer must be in each extension
    if HAS_KILLER:
        for X in updated_extensions:
            killer = get_negative_target_killer(args)
            clauses.append([membership_SAT_variables(killer, X, args, nb_updated_extensions)])

    if DEBUG:
        print("--")
    return clauses

### Encode remaining credulously accepted arguments
def remaining_credulously_accepted_arguments(args, neg_target, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG=False):
    if DEBUG:
        print("-- Credulously accepted arguments remain")
    clauses = []
    # Clauses 2 from paper
    for argument in args:
        if (argument not in neg_target) and is_credulously_accepted(argument, initial_extensions):
            new_clause = []
            for X in updated_extensions:
                new_clause.append(membership_SAT_variables(argument, X, args, nb_updated_extensions))
            clauses.append(new_clause)
            if DEBUG:
                print(clauses[-1])
    if DEBUG:
        print("--")
    return clauses

### Encode strict version
def strict_version(target, args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG=False):
    # Clauses 3 from paper, only for strict
    if DEBUG:
        print("-- Strict version: no new credulously accepted argument")    
    clauses = []
    for argument in args:
        if (argument not in target) and (not is_credulously_accepted(argument, initial_extensions)):
            for X in updated_extensions:
                clauses.append([-membership_SAT_variables(argument, X, args, nb_updated_extensions)])
                if DEBUG:
                    print(clauses[-1])
    if DEBUG:
        print("--")
    return clauses


# Clauses from Extension enforcement by Niskanen et al
def encode_conflict_freeness(args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG=False):
    ## First part: conflict-freeness
    if DEBUG:
        print("-- Conflict-freeness")
    clauses = []
    for extension in updated_extensions:
        for argument_a in args:
            for argument_b in args:
                clauses.append([-r_SAT_variables(argument_a, argument_b, extension, args, nb_updated_extensions),-membership_SAT_variables(argument_a, extension, args, nb_updated_extensions),-membership_SAT_variables(argument_b, extension, args, nb_updated_extensions)])
                if DEBUG:
                    print(clauses[-1])
    if DEBUG:
        print("--")
    return clauses

def encode_def_variables(args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG=False):
    ## Second part: semantics of def-variables
    if DEBUG:
        print("-- def variables")
    clauses = []
    for extension in updated_extensions:
        for argument_a in args:
            for argument_b in args:
                clauses.append([-defeat_SAT_variables(argument_b, argument_a, extension, args, nb_updated_extensions),membership_SAT_variables(argument_b, extension, args, nb_updated_extensions)])
                clauses.append([-defeat_SAT_variables(argument_b, argument_a, extension, args, nb_updated_extensions),r_SAT_variables(argument_b, argument_a, extension, args, nb_updated_extensions)])
                clauses.append([-membership_SAT_variables(argument_b, extension, args, nb_updated_extensions),-r_SAT_variables(argument_b, argument_a, extension, args, nb_updated_extensions),defeat_SAT_variables(argument_b, argument_a, extension, args, nb_updated_extensions)])
                if DEBUG:
                    print(clauses[-3:])
    if DEBUG:
        print("--")
    return clauses

def encode_stability(args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG=False):
    ## Third part: stability
    if DEBUG:
        print("-- Stability")
    clauses = []
    for extension in updated_extensions:
        for argument_a in args:
            new_clause = [membership_SAT_variables(argument_a, extension, args, nb_updated_extensions)]
            for argument_b in args:
                new_clause.append(defeat_SAT_variables(argument_b, argument_a, extension, args, nb_updated_extensions))
            clauses.append(new_clause)
            if DEBUG:
                print(clauses[-1])
    if DEBUG:
        print("--")
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
## Returns a apx-string corresponding to the AF encoded in the model
def decode_model_as_af_WITH_KILLER(model,args,nb_updated_extensions):
    result = ""
    for argument in args:
        if argument != "KILLER":
            result += f"arg({argument}).\n"
    for attacker in args:
        if attacker != "KILLER":
            for target in args:
                if target != "KILLER":
                    if r_SAT_variables(attacker, target, 1, args, nb_updated_extensions) in model:
                        result += f"att({attacker},{target}).\n"
    return result

def decode_model_as_af(model,args,nb_updated_extensions):
    result = ""
    for argument in args:
        result += f"arg({argument}).\n"
    for attacker in args:
        for target in args:
            if r_SAT_variables(attacker, target, 1, args, nb_updated_extensions) in model:
                result += f"att({attacker},{target}).\n"
    return result

## Returns a list of args and list of atts corresponding to the AF encoded in the model
def decode_model_as_af_struct(model,args,nb_updated_extensions):
    atts = []
    for attacker in args:
        for target in args:
            if r_SAT_variables(attacker, target, 1, args, nb_updated_extensions) in model:
                atts.append([attacker,target])
    return args, atts
