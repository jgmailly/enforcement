import pygarg.parser as parser
import sys
import time

import pygarg.solvers as solvers

from pysat.solvers import Solver
from pysat.examples.fm import FM
from pysat.formula import WCNF
from pysat.card import *

import credulous_encoding
import util

import argparse

semantics_list = ["ST"]
problems_list = ["CEnfS", "CEnfNS", "OptCEnfS", "OptCEnfNS"]
formats_list = ["apx"]

argparser = argparse.ArgumentParser()
argparser.add_argument("af_file",help="the file containing the initial AF")
argparser.add_argument("query_file", help="the file containing the enforcement query")
argparser.add_argument("-v", "--verbose", help="increase output verbosity", action="store_true")
argparser.add_argument("-p", "--problem", help=f"the pair XX-YY with XX in {problems_list} and YY in {semantics_list}")
argparser.add_argument("-fo", "--format", help=f"the format of the AF file in {formats_list} (default: apx)", default="apx")
argparser.add_argument("-o", "--output", help="the output file for printing the new theory (the standard output is used if this option is not set)")
argparser.add_argument("-ne", "--nextensions", help="the expected number of extensions for the updated AF (default: the number of extensions of the initial AF)")
argparser.add_argument("-c", "--constraints", help="the constraints file indicating which (non-)attacks from the initial theory should remain")
argparser.add_argument("-bo", "--bounded", help="the threshold for bounded enforcement")
cli_args = argparser.parse_args()

if cli_args.problem == None:
    sys.exit("Missing CLI parameter -p")


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

DEBUG = False

target, neg_target, conjunctive_positive, conjunctive_negative = util.parse_query_file(cli_args.query_file)

### Add all the arguments in the C+ sets to the positive targets
for conjunct in conjunctive_positive:
    for argument in conjunct:
        target.append(argument)

conjunctive_size = len(conjunctive_positive)
tmp = 0
for conjunct_neg in conjunctive_negative:
    if len(conjunct_neg) > tmp:
        tmp = len(conjunct_neg)
conjunctive_size += tmp

# m
if conjunctive_size > len(initial_extensions):
    nb_updated_extensions = conjunctive_size
else:
    nb_updated_extensions = len(initial_extensions)
#nb_updated_extensions = len(initial_extensions)
    
if cli_args.nextensions != None:
    nb_updated_extensions = int(cli_args.nextensions)
updated_extensions = [x+1 for x in range(nb_updated_extensions)]

if DEBUG:
    print("--------------------")
    for argument in args:
        for extension in updated_extensions:
            print(f"x_({argument},{extension}) = {credulous_encoding.membership_SAT_variables(argument, extension, args, nb_updated_extensions)}")
    print("--------------------")
    print("--------------------")
    for attacker in args:
        for target in args:
            print(f"r_({attacker},{target}) = {credulous_encoding.r_SAT_variables(attacker, target, extension, args, nb_updated_extensions)}")
    print("--------------------")
    print("--------------------")
    for X in updated_extensions:
        for attacker in args:
            for target in args:
                print(f"def_({attacker},{target},{X}) = {credulous_encoding.defeat_SAT_variables(attacker, target, X, args, nb_updated_extensions)}")
    print("--------------------")


#target, neg_target, conjunctive_positive, conjunctive_negative = util.parse_query_file(cli_args.query_file)

if cli_args.verbose:
    print(f"target = {target}")
    print(f"neg_target = {neg_target}")
    print(f"conjunctive_positive = {conjunctive_positive}")
    print(f"conjunctive_negative = {conjunctive_negative}")

clauses = credulous_encoding.encode_target(target,args, nb_updated_extensions, updated_extensions, DEBUG)
clauses += credulous_encoding.encode_negative_target(neg_target,args, nb_updated_extensions, updated_extensions, DEBUG)
clauses += credulous_encoding.remaining_credulously_accepted_arguments(args, neg_target, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG)
clauses += credulous_encoding.encode_conflict_freeness(args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG)
clauses += credulous_encoding.encode_def_variables(args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG)
clauses += credulous_encoding.encode_stability(args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG)
clauses += credulous_encoding.encode_no_self_attacks(args,atts,1, nb_updated_extensions)


if cli_args.constraints != None:
    constraints_file = cli_args.constraints
    constrained_atts, constrained_non_atts = util.parse_constraints_file(constraints_file)
    for att in constrained_atts:
        clauses.append([credulous_encoding.r_SAT_variables(att[0], att[1], 1, args, nb_updated_extensions)])
    for non_att in constrained_non_atts:
        clauses.append([-credulous_encoding.r_SAT_variables(non_att[0], non_att[1], 1, args, nb_updated_extensions)])


if cli_args.bounded != None:
    #print(f"bound = {cli_args.bounded}")
    bound_threshold = float(cli_args.bounded)
    bound_value = int(bound_threshold * len(args) * len(args))
    card_literals = []
    for attacker in args:
        for target in args:
            if [attacker,target] in atts:
                card_literals.append(-credulous_encoding.r_SAT_variables(attacker, target, 1, args, nb_updated_extensions))
            else:
                card_literals.append(credulous_encoding.r_SAT_variables(attacker, target, 1, args, nb_updated_extensions))
    last_SAT_var = credulous_encoding.defeat_SAT_variables(args[-1], args[-1], nb_updated_extensions, args, nb_updated_extensions)
    card_constraint = CardEnc.atmost(card_literals,bound=bound_value,top_id=last_SAT_var)
    #print(f"last_SAT_var = {last_SAT_var}")
    #print(f"card_constraint.clauses = {card_constraint.clauses}")
    clauses += card_constraint.clauses


def strict_problem(problem):
    return problem in ["CEnfS", "OptCEnfS"] 

def decision_problem(problem):
    return problem in ["CEnfS", "CEnfNS"]

def optimization_problem(problem):
    return problem in ["OptCEnfS", "OptCEnfNS"]

if strict_problem(problem) :
    clauses += credulous_encoding.strict_version(target, args, nb_updated_extensions, updated_extensions, initial_extensions, DEBUG)

time_start_enforcement = time.time()
model = None

SAT_result = "UNSAT"



### Returns the clause corresponding to the negation of a model
def forbid_model(model):
    clause = []
    for literal in model:
        clause.append(-literal)
    return clause

solution_cost = None


if decision_problem(problem):
    s = Solver(name='g4')
    for clause in clauses:
        s.add_clause(clause)

    model = None
    if s.solve():
        SAT_result = "SAT"
        model = s.get_model()

    s.delete()

    while model != None and (credulous_encoding.check_counterexample(model, args, neg_target, conjunctive_positive, conjunctive_negative, nb_updated_extensions, semantics) or (strict_problem(problem) and credulous_encoding.check_counterexample_strict_version(model, args, target, nb_updated_extensions, initial_extensions, semantics))):
        s = Solver(name='g4')
        clauses.append(forbid_model(model))
        for clause in clauses:
            s.add_clause(clause)

        if s.solve():
            SAT_result = "SAT"
            model = s.get_model()
        else:
            model = None
        s.delete()
        
elif optimization_problem(problem):
    wcnf = WCNF()
    for clause in clauses:
        wcnf.append(clause)
        
    soft_clauses = credulous_encoding.encode_graph_minimal_change(args, atts, nb_updated_extensions, DEBUG)
    for soft_clause in soft_clauses:
        wcnf.append(soft_clause, weight=1)

    nb_models = 0
    s = FM(wcnf, verbose = 0)
    if s.compute():
        SAT_result = "SAT"
        model = s.model
        nb_models+=1
        solution_cost = s.cost
    s.delete()
    while model != None and (credulous_encoding.check_counterexample(model, args, neg_target, conjunctive_positive, conjunctive_negative, nb_updated_extensions, semantics) or (strict_problem(problem) and credulous_encoding.check_counterexample_strict_version(model, args, target, nb_updated_extensions, initial_extensions, semantics))):
        nb_models+=1
        wcnf.append(forbid_model(model))
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
    
if model != None:
    if DEBUG:
        print(model)
    if cli_args.output == None:
        print(credulous_encoding.decode_model_as_af(model,args,nb_updated_extensions))
    else:
        with open(cli_args.output, 'w') as output_file:
            print(credulous_encoding.decode_model_as_af(model,args,nb_updated_extensions), file = output_file)

    if solution_cost == None:
        solution_cost = 0
        updated_args, updated_atts = credulous_encoding.decode_model_as_af_struct(model,args,nb_updated_extensions)
        for att in atts:
            if att not in updated_atts:
                solution_cost += 1
        for att in updated_atts:
            if att not in atts:
                solution_cost += 1


#print(f"{SAT_result} - Enumeration Time = {enumeration_time} - Enforcement Time = {enforcement_time} - Total Time = {enumeration_time+enforcement_time} - Solution cost = {solution_cost}")
print(f"{SAT_result},{enumeration_time+enforcement_time},{solution_cost}")
