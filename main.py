import pygarg.parser as parser
import sys
import pygarg.solvers as solvers
import time
from pysat.solvers import Solver
from encoding import *

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

#print(f"Enumeration Time = {enumeration_time} - Extensions = {initial_extensions} - Argument Name = {argname}")

DEBUG = False

# m
nb_updated_extensions = 2
updated_extensions = [x+1 for x in range(nb_updated_extensions)]

if DEBUG:
    print("--------------------")
    for argument in args:
        for extension in updated_extensions:
            print(f"x_({argument},{extension}) = {membership_SAT_variables(argument, extension, args, nb_updated_extensions)}")
    print("--------------------")
    print("--------------------")
    for attacker in args:
        for target in args:
            print(f"r_({attacker},{target}) = {r_SAT_variables(attacker, target, extension, args, nb_updated_extensions)}")
    print("--------------------")
    print("--------------------")
    for X in updated_extensions:
        for attacker in args:
            for target in args:
                print(f"def_({attacker},{target},{X}) = {defeat_SAT_variables(attacker, target, X, args, nb_updated_extensions)}")
    print("--------------------")

target = [argname]

clauses = encode_target(target,args, nb_updated_extensions, updated_extensions, DEBUG) + remaining_credulously_accepted_arguments(args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG) + encode_conflict_freeness(args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG) + encode_def_variables(args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG) + encode_stability(args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG)

if problem == "V1s":
    clauses += strict_version(target, args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG)

#print("Clauses = ", clauses)

time_start_enforcement = time.time()
s = Solver(name='g4')
for clause in clauses:
    s.add_clause(clause)



model = None
SAT_result = "UNSAT"
if s.solve():
    SAT_result = "SAT"
    model = s.get_model()

enforcement_time = time.time() - time_start_enforcement
print(f"{SAT_result} - Enumeration Time = {enumeration_time} - Enforcement Time = {enforcement_time} - Total Time = {enumeration_time+enforcement_time}")
    
if model != None:
    #print(model)
    print(decode_model_as_af(model,args,nb_updated_extensions))



s.delete()
