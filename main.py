import pygarg.parser as parser
import sys
import pygarg.solvers as solvers
import time
from pysat.solvers import Solver
from pysat.examples.fm import FM
from pysat.formula import WCNF
from encoding import *
import util

import argparse

semantics_list = ["ST"]
problems_list = ["V1s", "V1ns", "OptV1s", "OptV1ns"]
formats_list = ["apx"]

argparser = argparse.ArgumentParser()
argparser.add_argument("af_file",help="the file containing the initial AF")
argparser.add_argument("query_file", help="the file containing the enforcement query")
argparser.add_argument("-v", "--verbose", help="increase output verbosity", action="store_true")
argparser.add_argument("-p", "--problem", help=f"the pair XX-YY with XX in {problems_list} and YY in {semantics_list}")
argparser.add_argument("-fo", "--format", help=f"the format of the AF file in {formats_list}", default="apx")
argparser.add_argument("-o", "--output", help=f"the output file for printing the new theory")
cli_args = argparser.parse_args()

if cli_args.problem == None:
    sys.exit("Missing CLI parameter -p")


argname = "A"
apx_file = cli_args.af_file
task = cli_args.problem
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


target, neg_target, conjunctive_positive, conjunctive_negative = util.parse_query_file(cli_args.query_file)

if cli_args.verbose:
    print(f"target = {target}")
    print(f"neg_target = {neg_target}")
    print(f"conjunctive_positive = {conjunctive_positive}")
    print(f"conjunctive_negative = {conjunctive_negative}")

clauses = encode_target(target,args, nb_updated_extensions, updated_extensions, DEBUG)
clauses += encode_negative_target(neg_target,args, nb_updated_extensions, updated_extensions, DEBUG)
clauses += remaining_credulously_accepted_arguments(args, neg_target, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG)
clauses += encode_conflict_freeness(args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG)
clauses += encode_def_variables(args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG)
clauses += encode_stability(args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG)
clauses += encode_no_self_attacks(args,atts,1, nb_updated_extensions)

if problem in ["V1s","OptV1s"] :
    clauses += strict_version(target, args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG)

#print("Clauses = ", clauses)

def decision_problem(problem):
    return problem in ["V1s", "V1ns"]

def optimization_problem(problem):
    return problem in ["OptV1s", "OptV1ns"]

time_start_enforcement = time.time()
model = None

SAT_result = "UNSAT"

#### Returns True iff the current model is a counter-example, i.e. some arguments in the negative target are credulously accepted
def check_counterexample_negative_target(model, args, neg_target, nb_updated_extensions,semantics):
    #print("Check negative target")
    args, atts = decode_model_as_af_struct(model,args,nb_updated_extensions)
    for neg_arg in neg_target:
        if solvers.credulous_acceptability(args,atts,neg_arg,semantics):
            #print(f"Negative target {neg_arg} is accepted")
            return True
        #print(f"Negative target {neg_arg} is not accepted")
    return False

#### Returns True iff the current model is a counter-example for the conjunctive positive targets,
#### i.e. some set of arguments should appear together in an extension but its not the case
def check_counterexample_conjunctive_positive(model, args, conjunctive_positive, nb_updated_extensions, semantics):
    #print("Check conjunctive positive")
    args, atts = decode_model_as_af_struct(model,args,nb_updated_extensions)
    for conjunct in conjunctive_positive:
        if not solvers.credulous_acceptability_set(args,atts,conjunct,semantics):
            print(f"Conjunct {conjunct} is not credulously accepted")
            #print(decode_model_as_af(model,args,nb_updated_extensions))
            return True
        #print(f"Conjunct {conjunct} is credulously accepted")
    return False

#### Returns True iff the current model is a counter-example for the conjunctive negative targets,
#### i.e. some set of arguments should not appear together in an extension but they do
def check_counterexample_conjunctive_negative(model, args, conjunctive_negative, nb_updated_extensions, semantics):
    #print("Check conjunctive negative")    
    args, atts = decode_model_as_af_struct(model,args,nb_updated_extensions)
    for conjunct in conjunctive_negative:
        if solvers.credulous_acceptability_set(args,atts,conjunct,semantics):
            #print(f"Conjunct {conjunct} is credulously accepted")
            #print(decode_model_as_af(model,args,nb_updated_extensions))
            #sys.exit("FIN")
            return True
        #print(f"Conjunct {conjunct} is not credulously accepted")
    return False

### Returns the clause corresponding to the negation of a model
def forbid_model(model):
    clause = []
    for literal in model:
        clause.append(-literal)
    return clause

solution_cost = None

#forbidden_models = []

if decision_problem(problem):
    s = Solver(name='g4')
    for clause in clauses:
        s.add_clause(clause)
        
    if s.solve():
        SAT_result = "SAT"
        model = s.get_model()

    s.delete()
    
elif optimization_problem(problem):
    wcnf = WCNF()
    for clause in clauses:
        wcnf.append(clause)

    soft_clauses = encode_graph_minimal_change(args, atts, nb_updated_extensions, DEBUG)
    for soft_clause in soft_clauses:
        wcnf.append(soft_clause, weight=1)
        
    s = FM(wcnf, verbose = 0)
    if s.compute():
        SAT_result = "SAT"
        model = s.model
        solution_cost = s.cost
    s.delete()
    nbModels = 1
    while model != None and (check_counterexample_negative_target(model, args, neg_target, nb_updated_extensions,semantics) or check_counterexample_conjunctive_positive(model, args, conjunctive_positive, nb_updated_extensions, semantics) or check_counterexample_conjunctive_negative(model, args, conjunctive_negative, nb_updated_extensions, semantics)):
        #if model in forbidden_models:
            #sys.exit("PROBLEM WITH FORBIDDEN MODELS")
        wcnf.append(forbid_model(model))
        #forbidden_models.append(model)
        #print(f"NbModels = {nbModels} - Forbidden model = {model}")
        nbModels += 1
        s = FM(wcnf, verbose = 0)
        SAT_result = "UNSAT"
        solution_cost = None
        if s.compute():
            SAT_result = "SAT"
            model = s.model
            solution_cost = s.cost
        else:
            model = None
        s.delete()
else:
    sys.exit(f"Unsupported problem: {problem}")

if model == None:
    solution_cost = None

enforcement_time = time.time() - time_start_enforcement
print(f"{SAT_result} - Enumeration Time = {enumeration_time} - Enforcement Time = {enforcement_time} - Total Time = {enumeration_time+enforcement_time} - Solution cost = {solution_cost}")
    
if model != None:
    if DEBUG:
        print(model)
    if cli_args.output == None:
        print(decode_model_as_af(model,args,nb_updated_extensions))
    else:
        with open(cli_args.output, 'w') as output_file:
            print(decode_model_as_af(model,args,nb_updated_extensions), file = output_file)



