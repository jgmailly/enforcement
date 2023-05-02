import sys
import random
import argparse

# 0.3-0.4 symmetric, 0.25-0.3 for each direction and 0.1-0.15 no attacks
argparser = argparse.ArgumentParser()
argparser.add_argument("-n", "--nargs", help="the number of arguments (default: 100)", default="100")
argparser.add_argument("-p1", "--proba1", help="the first probability (a1->a2, default: 0.25)", default="0.25")
argparser.add_argument("-p2", "--proba2", help="the second probability (a2->a1, default: 0.25)", default="0.25")
argparser.add_argument("-p3", "--proba3", help="the third probability (symmetric attack, default: 0.35)", default="0.35")
argparser.add_argument("-p4", "--proba4", help="the fourth probability (no attack, default: 0.15)", default="0.15")
cli_args = argparser.parse_args()

proba1 = float(cli_args.proba1)
proba2 = float(cli_args.proba2)
proba_symmetric = float(cli_args.proba3)
proba_no_attack = float(cli_args.proba4)
nb_args = int(cli_args.nargs)

if proba1 + proba2 + proba_symmetric + proba_no_attack != 1:
    sys.exit("Incorrect probabilities")

apx_result=""

for i in range(1,nb_args+1):
    apx_result += f"arg(a{i}).\n"


for i in range(1,nb_args+1):
    for j in range(i+1, nb_args+1):
        random_number = random.random()
        if random_number < proba1:
            apx_result += f"att(a{i},a{j}).\n"
        elif random_number < proba1 + proba2 :
            apx_result += f"att(a{j},a{i}).\n"
        elif random_number < proba1 + proba2 + proba_symmetric :
            apx_result += f"att(a{i},a{j}).\n"
            apx_result += f"att(a{j},a{i}).\n"

print(apx_result,end='')
