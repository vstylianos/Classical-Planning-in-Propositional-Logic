import os
import re
from pysat.solvers import Solver
from pysat.formula import CNF

__FD_PLAN_CMD__ = "./fdplan.sh {} {}"
__FD_PLAN_COST_CMD__ = "./get_plan_cost.sh {} {}"


def get_plan(domainFileName, problemFileName):
	output = os.popen(__FD_PLAN_CMD__.format(domainFileName, problemFileName)).read().strip()
	plan   = [item.strip() for item in output.split('\n')] if output != '' else []
	if len(plan) > 0:
		output = os.popen(__FD_PLAN_COST_CMD__).read().strip()
		cost   = int(output)
	else:
		cost = 0
	return plan, cost


def makeName(name):
    v = str(name)
    v = re.sub('[\\{\}()<>-]', ' ', v)
    v = v.strip()
    v = v.replace('-', '')
    v = v.split(" ")
    Name = '_'.join(v)
    Name = Name.upper()
    return Name

def make_step(name, step):
    return str(name) + "_" + str(step)


def remove_steps(name):
    v = str(name).lower()
    v = re.sub('[\\{\}<>-_()]', ' ', v)
    v = v.replace('-', '')
    v = v.strip()
    v = v[:v.find(" ")]
    return str(v)


def getStep(var_name):
    [_, step] = var_name.split("_")
    return int(step)


def getAct(var_name):
    if type(var_name) is list:
        all_var = [Bool(str(v).rstrip("_0123456789")) for v in var_name ]
        return all_var
    else:
        var_name = str(var_name)
        name= var_name.rstrip("_0123456789")

        return Bool(str(name))



class planningKB():

	def __init__(self, horizon, fluent_vars, action_vars, fluents_all_steps, actions_all_steps, vars, inits, goals, preconds, add_effects, del_effects, frame_axioms, excls):

		self.horizon = horizon
		self.fluent_vars = fluent_vars
		self.action_vars = action_vars
		self.actions_all_steps = actions_all_steps
		self.fluents_all_steps = fluents_all_steps
		self.variables = vars
		self.inits = inits
		self.goals = goals
		self.preconditions = preconds
		self.add_effects = add_effects
		self.del_effects = del_effects
		self.excls = excls
		self.frame_axioms = frame_axioms



	def all_formulae(self):
		return self.inits + self.goals + self.preconditions +self.add_effects +self.del_effects + self.frame_axioms + self.excls


	def get_id_from_name(self, obj):
		return self.variables[obj]


	def get_name_from_id(self, id):
		for key, value in self.variables.items():
			if value == id:
				return key

	def get_plan(self):
		plan = []

		with Solver(name='MiniSat22', bootstrap_with=self.all_formulae()) as s:
			if s.solve() == True:
				m = s.get_model()
				for i in m:
					if i > 0 and self.get_name_from_id(i) in self.actions_all_steps:
						plan.append(self.get_name_from_id(i))
			return plan



	def skeptical_entailment(self, query):
		with Solver(name='MiniSat22', bootstrap_with=self.all_formulae()) as s:
			# add negation of query
			s.append_formula(query.negate().clauses)
			if s.solve() == False:
				return True
			else:
				return False

	def sat(self, query):
		if query:
			with Solver(name='MiniSat22', bootstrap_with=self.all_formulae() + query.clauses) as s:
				if s.solve():
					return True
				else:
					return False
		else:
			with Solver(name='MiniSat22', bootstrap_with=self.all_formulae()) as s:
				if s.solve():
					return True
				else:
					return False
		

	def get_model(self):
		with Solver(name='MiniSat22', bootstrap_with=self.all_formulae()) as s:
			if s.solve() == True:
				return s.get_model()
			else:
				return None



def construct_query(KB, literals):
	query = CNF()
	for l in literals:
		query.append([KB.get_id_from_name(l)])
	return query


def map_id_to_vars(KB, nested_list):
	return [["Not "+KB.get_name_from_id(abs(i)) if i<0 else KB.get_name_from_id(abs(i)) for i in ne] for ne in nested_list]
