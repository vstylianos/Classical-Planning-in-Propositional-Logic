from collections import defaultdict
import utils
from pysat.formula import IDPool, CNF


'''
Basic encoding of classical planning problems with non-durative actions and positive preconditions. The knowledge base is in CNF form.
'''

class Encoder():

	def __init__(self, task, horizon):
		self.task = task
		self.horizon = horizon
		self.cnf = CNF()
		self.vpool = IDPool()
		self.var = lambda i: self.vpool.id('{0}'.format(i))
		self.checked = defaultdict()

	def createVariables(self):
		"""
		Allocate 2 lists:
		- boolean variables
		- action variable

		Then create IDs for the variables
		"""
		self.actions = self.task.operators

		self.boolean_variables = []
		for fluent in self.task.facts:
			ground_name = utils.makeName(fluent)
			# lifted_name = utils.remove_steps([ground_name])
			self.boolean_variables.append(ground_name)

		self.action_variables = []
		for action in self.actions:
			ground_name = utils.makeName(action.name)
			# lifted_name = utils.remove_steps([ground_name])
			self.action_variables.append(ground_name)

		self.actions_all_steps = set()
		self.fluents_all_steps = set()
		for t in range(self.horizon):
			for a in self.action_variables:
				self.actions_all_steps.add(utils.make_step(a, t))
			for f in self.boolean_variables:
				self.fluents_all_steps.add(utils.make_step(f, t))


	def encodeInitialState(self):
		"""
		Encodes the initial states.
		"""
		self.initial = []
		for fact in self.task.initial_state:
			init = utils.make_step(utils.makeName(fact), 0)

			if self.var(init) not in self.checked.values():
				self.checked[init] = self.vpool.id('{0}'.format(init))

			self.initial.append([self.var(init)])

		for var_name in self.boolean_variables:
			v = utils.make_step(utils.makeName(var_name), 0)
			if self.var(v) not in self.checked.values():
				self.checked[v] = self.vpool.id('{0}'.format(v))
			if not [self.var(v)] in self.initial:
				self.initial.append([-self.var(v)])


	## Encode formula defining goal state
	def encodeGoalState(self):
		"""
		Encodes the initial states.
		"""
		self.goals = []

		for fact in self.task.goals:
			goal = utils.make_step(utils.makeName(fact), self.horizon)
			if self.var(goal) not in self.checked.values():
				self.checked[goal] = self.vpool.id('{0}'.format(goal))
			self.goals.append([self.var(goal)])


	def encodeActions(self):
		"""
		Encodes Action Axioms.
		"""

		self.preconditions = []
		self.addition_effects = []
		self.deletion_effects = []

		for t in range(self.horizon):
			for action in self.actions:
				ground_name = utils.makeName(action.name)
				ground_name_time = utils.make_step(ground_name, t)
				if self.var(ground_name_time) not in self.checked.values():
					self.checked[ground_name_time] = self.vpool.id('{0}'.format(ground_name_time))
				# Encode preconditions
				for pre in action.preconditions:
					ground_pre_name = utils.makeName(pre)
					ground_pre_name_time = utils.make_step(ground_pre_name, t)
					if self.var(ground_pre_name_time) not in self.checked.values():
						self.checked[ground_pre_name_time] = self.vpool.id('{0}'.format(ground_pre_name_time))
					self.preconditions.append([-self.var(ground_name_time), self.var(ground_pre_name_time)])

				# Encode add effects
				for add in action.add_effects:
					ground_add_name = utils.makeName(add)
					ground_add_name_time = utils.make_step(ground_add_name, t + 1)
					if self.var(ground_add_name_time) not in self.checked.values():
						self.checked[ground_add_name_time] = self.vpool.id('{0}'.format(ground_add_name_time))
					self.addition_effects.append([-self.var(ground_name_time), self.var(ground_add_name_time)])

				# Encode del effects
				for dele in action.del_effects:
					ground_del_name = utils.makeName(dele)
					ground_del_name_time = utils.make_step(ground_del_name, t + 1)
					if self.var(ground_del_name_time) not in self.checked.values():
						self.checked[ground_del_name_time] = self.vpool.id('{0}'.format(ground_del_name_time))
					self.deletion_effects.append([-self.var(ground_name_time), -self.var(ground_del_name_time)])


	# Encode explanatory Frame Axioms:
	def encodeFrame(self):
		"""
		Encodes the Explanatory Frame Axioms
		"""
		self.frame_axioms = []

		for t in range(self.horizon):
			# Encode frame axioms for boolean fluents
			for fluent in self.task.facts:
				action_del_fluent = []
				action_add_fluent = []

				for action in self.actions:
					# Check if f is in add of some action
					if fluent in action.add_effects:
						ground_name = utils.makeName(action.name)
						ground_name = utils.make_step(ground_name, t)
						if self.var(ground_name) not in self.checked.values():
							self.checked[ground_name] = self.vpool.id('{0}'.format(ground_name))

						action_add_fluent.append(ground_name)
					elif fluent in action.del_effects:
						ground_name = utils.makeName(action.name)
						ground_name = utils.make_step(ground_name, t)
						if self.var(ground_name) not in self.checked.values():
							self.checked[ground_name] = self.vpool.id('{0}'.format(ground_name))
						action_del_fluent.append(ground_name)

				# Explanatory Frame Axiom:
				# If action_del_fluent is not zero: ((f_i & -f_i+1) -> Or(a_i))
				if len(action_del_fluent) is not 0:
					del_action = [self.var(a) for a in action_del_fluent]
					ground_fluent_i = utils.make_step(utils.makeName(fluent), t)
					if self.var(ground_fluent_i) not in self.checked.values():
						self.checked[ground_fluent_i] = self.vpool.id('{0}'.format(ground_fluent_i))
					ground_fluent_i_plus_1 = utils.make_step(utils.makeName(fluent), t + 1)
					if self.var(ground_fluent_i_plus_1) not in self.checked.values():
						self.checked[ground_fluent_i_plus_1] = self.vpool.id('{0}'.format(ground_fluent_i_plus_1))


					frame = [-self.var(ground_fluent_i), self.var(ground_fluent_i_plus_1)]
					expl_axiom = frame+del_action
					self.frame_axioms.append(expl_axiom)

				# Else ~fluent_i or fluent_i_plus_1
				else:
					ground_fluent_i = utils.make_step(utils.makeName(fluent), t)
					if self.var(ground_fluent_i) not in self.checked.values():
						self.checked.add(self.vpool.id('{0}'.format(ground_fluent_i)))
						self.checked[ground_fluent_i] = self.vpool.id('{0}'.format(ground_fluent_i))

					ground_fluent_i_plus_1 = utils.make_step(utils.makeName(fluent), t + 1)
					if self.var(ground_fluent_i_plus_1) not in self.checked.values():
						self.checked[ground_fluent_i_plus_1] = self.vpool.id('{0}'.format(ground_fluent_i_plus_1))
					frame = [-self.var(ground_fluent_i), self.var(ground_fluent_i_plus_1)]
					self.frame_axioms.append(frame)

				# If action_add_fluent is not zero: ((-f_i & f_i+1) -> Or(a_i))
				if len(action_add_fluent) is not 0:
					# add_action = Or([Bool(k) for k in action_add_fluent])
					add_action = [self.var(a) for a in action_add_fluent]
					ground_fluent_i = utils.make_step(utils.makeName(fluent), t)
					if self.var(ground_fluent_i) not in self.checked.values():
						self.checked[ground_fluent_i] = self.vpool.id('{0}'.format(ground_fluent_i))

					ground_fluent_i_plus_1 = utils.make_step(utils.makeName(fluent), t + 1)
					if self.var(ground_fluent_i_plus_1) not in self.checked.values():
						self.checked[ground_fluent_i_plus_1] = self.vpool.id('{0}'.format(ground_fluent_i_plus_1))

					frame = [self.var(ground_fluent_i), -self.var(ground_fluent_i_plus_1)]
					expl_axiom = frame + add_action
					self.frame_axioms.append(expl_axiom)

				# Else fluent_i or ~fluent_i_plus_1
				else:
					ground_fluent_i = utils.make_step(utils.makeName(fluent), t)
					if self.var(ground_fluent_i) not in self.checked.values():
						self.checked.add(self.vpool.id('{0}'.format(ground_fluent_i)))
						self.checked[ground_fluent_i] = self.vpool.id('{0}'.format(ground_fluent_i))

					ground_fluent_i_plus_1 = utils.make_step(utils.makeName(fluent), t + 1)
					if self.var(ground_fluent_i_plus_1) not in self.checked.values():
						self.checked[ground_fluent_i_plus_1] = self.vpool.id('{0}'.format(ground_fluent_i_plus_1))
					frame = [self.var(ground_fluent_i), -self.var(ground_fluent_i_plus_1)]
					self.frame_axioms.append(frame)


	## Encode The Execution Semantics
	def encodeExecutionSemantics(self):
		"""
		Encodes the action mutexes (linear execution). Can be modified to do parallel execution.
		"""

		mutexes = []

		for step in range(self.horizon):
			for a1 in self.actions:
				for a2 in self.actions:
					if not a1.name == a2.name:
						A1 = utils.make_step(utils.makeName(a1.name), step)
						if self.var(A1) not in self.checked.values():
							self.checked[A1] = self.vpool.id('{0}'.format(A1))
						A2 = utils.make_step(utils.makeName(a2.name), step)
						if self.var(A2) not in self.checked.values():
							self.checked[A2] = self.vpool.id('{0}'.format(A2))

						mutexes.append([-self.var(A1), -self.var(A2)])
		return mutexes


	# Encode the propositional formulae
	def encode(self):
		"""
		Encode the KB.
		"""
		# Create variables
		self.createVariables()

		# Encode initial state axioms
		self.encodeInitialState()

		# # Encode goal state axioms
		self.encodeGoalState()

		# Encode universal axioms
		self.encodeActions()

		# # Encode explanatory frame axioms
		self.encodeFrame()

		# Encode execution semantics (lin/par)
		excls = self.encodeExecutionSemantics()

		KB = utils.planningKB(self.horizon, self.boolean_variables, self.action_variables, self.fluents_all_steps, self.actions_all_steps, self.checked, self.initial, self.goals, self.preconditions, self.addition_effects, self.deletion_effects,
						self.frame_axioms, excls)
		return KB

