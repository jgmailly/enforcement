import pygarg.parser as parser
import sys
import pygarg.solvers as solvers
import time        

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

#### SAT Variables
# Assume we have the initial theory T = (A,R) with |A| = k.
# x_{a_i, E_X'} -> (i-1)*k + X
# For each E_X', we need k + k*k variables:
## x_{ai} -> m*m + (X-1)(k+k*k) + i
## r_{ai,aj} -> m*m + (X-1)(k+k*k) + k + (i-1)*k + j

# m
nb_updated_extensions = 5
updated_extensions = [x+1 for x in range(nb_updated_extensions)]

def membership_SAT_variables(argument, extension, args, nb_updated_extensions):
    # argument : argument name
    # extension : extension index between 1 and nb_udated_extensions (included)
    i = args.index(argument) + 1
    return (i-1) * nb_updated_extensions + extension

#print("--------------------")
#for argument in args:
#    for extension in updated_extensions:
#        print(f"x_({argument},{extension}) = {membership_SAT_variables(argument, extension, args, nb_updated_extensions)}")
#print("--------------------")

def x_SAT_variables(argument, extension, args, nb_updated_extensions):
    m = nb_updated_extensions
    k = len(args)
    i = args.index(argument) + 1
    return (m * m) + (extension - 1) * (k+k*k) + i

#print("--------------------")
#for extension in updated_extensions:
#        for argument in args:
#                print(f"x_({argument}) = {x_SAT_variables(argument, extension, args, nb_updated_extensions)}")
#print("--------------------")

def r_SAT_variables(attacker, target, extension, args, nb_updated_extensions):
    m = nb_updated_extensions
    k = len(args)
    i = args.index(attacker) + 1
    j = args.index(target) + 1
    return (m * m) + (extension - 1) * (k+k*k) + k + (i-1)*k + j

#print("--------------------")
#for extension in updated_extensions:
#        for attacker in args:
#                for target in args:
#                        print(f"r_({attacker},{target}) = {r_SAT_variables(attacker, target, extension, args, nb_updated_extensions)}")
#print("--------------------")

clauses = []

## Clause 1 from paper
new_clause = []
for X in updated_extensions:
    new_clause.append(membership_SAT_variables(argname, X, args, nb_updated_extensions))
clauses.append(new_clause)

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

for argument in args:
    if is_credulously_accepted(argument, initial_extensions):
        new_clause = []
        for X in updated_extensions:
            new_clause.append(membership_SAT_variables(argument, X, args, nb_updated_extensions))
        clauses.append(new_clause)

print("Clauses = ", clauses)
