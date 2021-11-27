from pyperplan import Parser, grounding
from CNF_Encoder import Encoder
from utils import *

# ----------------------------------------------------------------------------------------------------------------------


''' Parse PDDL domain and problem.
'''
# Agent's domain:
path_domain_agent = 'blocks/original_domain.pddl'
# Problem file:
path_instance = 'blocks/prob1.pddl'

# Parse domain:
parser_agent = Parser(path_domain_agent, path_instance)
domain_agent = parser_agent.parse_domain()
problem_agent = parser_agent.parse_problem(domain_agent)
task_agent = grounding.ground(problem_agent)


'''Use fast-downward planner to get horizon of shortest plan.
'''
Plan, horizon = get_plan(path_domain_agent, path_instance)
print("Optimal plan horizon :", horizon)
print(Plan)


'''Encode the knowledge bases. Horizon is taken from fast-downward optimal plan.
'''
# Encoded Knowledge Base:
KB = Encoder(task_agent, horizon).encode()


'''Get a plan from KB.
'''
plan = KB.get_plan()
print("Encoded KB plan:", plan)


query = CNF()
query.extend([[KB.get_id_from_name("PICKUP_B_0")],[KB.get_id_from_name("STACK_B_A_1")]])

print(KB.skeptical_entailment(query))