import pygarg.parser as parser
import sys
import pygarg.solvers as solvers
import time
from pysat.solvers import Solver

semantics_list = ["CF", "AD", "ST", "CO"]
problems_list = ["V1s", "V1ns"]
formats_list = ["apx"]
usage_message=f"Usage: python3 main.py -p <problem>-<semantics> -fo <format> -f <file> [-a <argname>]\n"
usage_message+=f"Possible semantics: {semantics_list}\n"
usage_message+=f"Possible problems: {problems_list}\n"
usage_message+=f"Possible formats: {formats_list}\n"

argname = ""
if len(sys.argv) > 7:
    argname = sys.argv[8]
apx_file = sys.argv[6]
task = sys.argv[2]
split_task = task.split("-")
problem = split_task[0]
semantics = split_task[1]

if problem not in problems_list:
    sys.exit(f"Problem {problem} not recognized. Supported problems: {problems_list}.")

if semantics not in semantics_list:
    sys.exit(f"Semantics {semantics} not recognized. Supported problems: {semantics_list}.")

args, atts = parser.parse(apx_file)
nb_args = len(args)

time_start_enumeration = time.time()
initial_extensions = solvers.extension_enumeration(args,atts,semantics)
enumeration_time = time.time() - time_start_enumeration

print(f"Enumeration Time = {enumeration_time} - Extensions = {initial_extensions} - Argument Name = {argname}")

#sys.exit("end")

#### SAT Variables
# Assume we have the initial theory T = (A,R) with |A| = k.
# x_{a_i, E_X'} -> (i-1)*k + X
# For building the updated theory, we need:
## r_{ai,aj} -> (m*k) + (i-1)*k + j
# For each E_X', we need k variables:
##### Maybe the last ones are not useful, think about it.
## def_{bi,ai, E_X'} -> (k*m + k*k) + (i-1)*k + X


# m
nb_updated_extensions = 2
updated_extensions = [x+1 for x in range(nb_updated_extensions)]

def membership_SAT_variables(argument, extension, args, nb_updated_extensions):
    # argument : argument name
    # extension : extension index between 1 and nb_udated_extensions (included)
    i = args.index(argument) + 1
    return (i-1) * nb_updated_extensions + extension

print("--------------------")
for argument in args:
    for extension in updated_extensions:
        print(f"x_({argument},{extension}) = {membership_SAT_variables(argument, extension, args, nb_updated_extensions)}")
print("--------------------")

def r_SAT_variables(attacker, target, extension, args, nb_updated_extensions):
    m = nb_updated_extensions
    k = len(args)
    i = args.index(attacker) + 1
    j = args.index(target) + 1
    return (m * k) + (i-1)*k + j

print("--------------------")
for attacker in args:
    for target in args:
        print(f"r_({attacker},{target}) = {r_SAT_variables(attacker, target, extension, args, nb_updated_extensions)}")
print("--------------------")


#### PROBABLY USELESS
def x_SAT_variables(argument, extension, args, nb_updated_extensions):
    m = nb_updated_extensions
    k = len(args)
    i = args.index(argument) + 1
    return (m*k + k*k) + (i - 1) * m + extension

#print("--------------------")
#for argument in args:
#    for extension in updated_extensions:
#        print(f"y_({argument},{extension}) = {x_SAT_variables(argument, extension, args, nb_updated_extensions)}")
#print("--------------------")

def defeat_SAT_variables(attacker, target, extension, args, nb_updated_extensions):
    k = len(args)
    m = nb_updated_extensions
    i = args.index(attacker) + 1
    j = args.index(target) + 1
    return (k*m) + (k*k) + (X-1)*k*k + (i-1)*k + j

print("--------------------")
for X in updated_extensions:
    for attacker in args:
        for target in args:
#            k = len(args)
#            m = nb_updated_extensions
#            i = args.index(attacker) + 1
#            j = args.index(target) + 1
            print(f"def_({attacker},{target},{X}) = {defeat_SAT_variables(attacker, target, extension, args, nb_updated_extensions)}")
print("--------------------")


clauses = []


## Clause 1 from paper
new_clause = []
for X in updated_extensions:
    new_clause.append(membership_SAT_variables(argname, X, args, nb_updated_extensions))
clauses.append(new_clause)
print(clauses[-1])

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

# Clauses 2 from paper
for argument in args:
    if is_credulously_accepted(argument, initial_extensions):
        new_clause = []
        for X in updated_extensions:
            new_clause.append(membership_SAT_variables(argument, X, args, nb_updated_extensions))
        clauses.append(new_clause)
        print(clauses[-1])

# Clauses 3 from paper, only for strict
if problem == "V1s":
    for argument in args:
        if (argument != argname) and (not is_credulously_accepted(argument, initial_extensions)):
            for X in updated_extensions:
                clauses.append([-membership_SAT_variables(argument, X, args, nb_updated_extensions)])
                print(clauses[-1])

###### TO DO
######### CORRECT THE LAST PART WITH NEW VARIABLES
                
# Clauses from Extension enforcement by Niskanen et al
for extension in updated_extensions:
    # Arguments from the extension must be in the target for enforcement
    for argument in args:
        clauses.append([membership_SAT_variables(argument, extension, args, nb_updated_extensions), -x_SAT_variables(argument, extension, args, nb_updated_extensions)])
        print(clauses[-1])
    # Arguments that are forbidden in the extension must not be in the target for enforcement
    for argument in args:
        clauses.append([-membership_SAT_variables(argument, extension, args, nb_updated_extensions), x_SAT_variables(argument, extension, args, nb_updated_extensions)])
        print(clauses[-1])
    # These clauses enforce conflict-freeness of the target for enforcement    
    for attacker in args:
        for target in args:
            clauses.append([-r_SAT_variables(attacker, target, extension, args, nb_updated_extensions), -x_SAT_variables(attacker, extension, args, nb_updated_extensions),-x_SAT_variables(target, extension, args, nb_updated_extensions)])
            print(clauses[-1])
    # These clauses enforce stability of the target for enforcement
    for argument in args:
        for other_argument in args:
            clauses.append([x_SAT_variables(argument, extension, args, nb_updated_extensions),x_SAT_variables(other_argument, extension, args, nb_updated_extensions)])
            print(clauses[-1])
            clauses.append([x_SAT_variables(argument, extension, args, nb_updated_extensions),r_SAT_variables(other_argument, argument, extension, args, nb_updated_extensions)])
            print(clauses[-1])
    
                
#print("Clauses = ", clauses)

time_start_enforcement = time.time()
s = Solver(name='g4')
for clause in clauses:
    s.add_clause(clause)
enforcement_time = time.time() - time_start_enforcement

def decode_model_as_af(model,args,nb_updated_extensions):
    result = ""
    for attacker in args:
        for target in args:
            if r_SAT_variables(attacker, target, extension, args, nb_updated_extensions) in model:
                result += f"att({attacker},{target}).\n"
            elif -r_SAT_variables(attacker, target, extension, args, nb_updated_extensions) in model:
                print("ok")
            else :
                print("ERROR!")
    return result

if s.solve():
    print("SAT")
    model = s.get_model()
    print(model)
    print(decode_model_as_af(model,args,nb_updated_extensions))
else:
    print("UNSAT")

s.delete()
