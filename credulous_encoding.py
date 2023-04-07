import pygarg.solvers as solvers

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


# Ensures that an argument which is not self-attacking in the initial theory will not become so in the updated theory
def encode_no_self_attacks(args,atts,extension, nb_updated_extensions):
    clauses = []
    for argument in args:
        if [argument,argument] not in atts:
            clauses.append([-r_SAT_variables(argument, argument, extension, args, nb_updated_extensions)])
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
    ## For each argument in the negative target, and each extension, add one unit clause to say that the argument is not in the extension
    if DEBUG:
        print("-- Negative target")
    clauses = []
    for argname in neg_target:
        for X in updated_extensions:
            clauses.append([-membership_SAT_variables(argname, X, args, nb_updated_extensions)])
            if DEBUG:
                print(clauses[-1])

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


#### Returns True iff the current model is a counter-example, i.e. some arguments in the negative target are credulously accepted
def check_counterexample_negative_target(model, args, neg_target, nb_updated_extensions,semantics):
    args, atts = decode_model_as_af_struct(model,args,nb_updated_extensions)
    for neg_arg in neg_target:
        if solvers.credulous_acceptability(args,atts,neg_arg,semantics):
            return True
    return False

#### Returns True iff the current model is a counter-example for the conjunctive positive targets,
#### i.e. some set of arguments should appear together in an extension but its not the case
def check_counterexample_conjunctive_positive(model, args, conjunctive_positive, nb_updated_extensions, semantics):
    args, atts = decode_model_as_af_struct(model,args,nb_updated_extensions)
    for conjunct in conjunctive_positive:
        if not solvers.credulous_acceptability_set(args,atts,conjunct,semantics):
            return True
    return False

#### Returns True iff the current model is a counter-example for the conjunctive negative targets,
#### i.e. some set of arguments should not appear together in an extension but they do
def check_counterexample_conjunctive_negative(model, args, conjunctive_negative, nb_updated_extensions, semantics):
    args, atts = decode_model_as_af_struct(model,args,nb_updated_extensions)
    for conjunct in conjunctive_negative:
        if solvers.credulous_acceptability_set(args,atts,conjunct,semantics):
            return True
    return False

#### Returns True iff the current model is a counter-example for the strict enforcement,
#### i.e. some argument which was not initially (credulously) accepted, and does not belong to the target,
#### is accepted in the updated theory.
def check_counterexample_strict_version(model, args, target, nb_updated_extensions, initial_extensions, semantics):
    args, atts = decode_model_as_af_struct(model,args,nb_updated_extensions)
    for argument in args:
        if (argument not in target) and (not is_credulously_accepted(argument, initial_extensions)):
            if solvers.credulous_acceptability(args,atts,argument,semantics):
                return True
    return False

def check_counterexample(model, args, neg_target, conjunctive_positive, conjunctive_negative, nb_updated_extensions, semantics):
    return check_counterexample_negative_target(model, args, neg_target, nb_updated_extensions,semantics) or check_counterexample_conjunctive_positive(model, args, conjunctive_positive, nb_updated_extensions, semantics) or check_counterexample_conjunctive_negative(model, args, conjunctive_negative, nb_updated_extensions, semantics)
