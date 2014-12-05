## Encoder.py
## Takes a list of Tasks, and returns whether or not the tasks can be completed, given a World

import z3
from z3 import Not, Or, And, If

class Task:
    # weight: a priority indicator for the task. Tasks with weight=0
    # ('hard tasks') will always be given priority over any task with
    # other weights ('soft tasks'), then other tasks will be assigned
    # to acheive the greatest sum of weights. That is, higher weights
    # mean more priority, but two tasks with weight 2 will outweigh a
    # task with weight 3, since 2+2=4>3. As a side affect of how
    # priority is calculated with regard to hard tasks, the solution
    # is not guaranteed to be optimal, in cases where there are
    # multiple ways to get the most hard tasks, and one of them would
    # allow more soft tasks.
    #
    # intervals: A list of pairs, where each pair cooresponds to an
    # interval in which the task can be completed. The first element
    # of the interval is the global time at which the interval starts,
    # and the second element is the global time at which the interval
    # ends. Global time can be relative to anything, as long as it is
    # consistent across calls, and uses the same time units as all
    # other time based numbers, like task duration and travel time.
    # As far as the solver is concerned, not getting a task done
    # during one of it's intervals is the same as not getting it done
    # at all.
    #
    # location: The location tag at which this task must be done.
    # these tags can be anything, as long as they are comparable with
    # == in python, and can be passed to the World.time method to get
    # the distance between two of them. Usually, I like to use
    # strings.
    #
    # taskID: a tag indicating the type of this task. Types are used
    # to lookup how long a task will take, but they are unconstrained
    # as long as they match the World you pass in.
    #
    # name: A string name of the task. This is not used for anything,
    # but exists for convenience.

    def __init__(self, weight, intervals, location, taskID, name):
        self.weight = weight
        assert(isinstance(intervals, list))
        self.intervals = intervals
        self.location = location
        self.ID = taskID
        self.name = name

    def __str__(self):
        return self.name

# A task class for specifying deadlines intstead of intervals.
class DeadlineTask(Task):
    def __init__(self, weight, deadline, location, taskID, name):
        assert(isinstance(deadline, int))
        super.__init__(weight, [(0,deadline)], location, taskID, name)

class World:
    # Get the time between two locations. Generally this should be
    # '90% time,' as in with 90% likelyhood, it will take less than or
    # equal to this amount of time.
    def time(self, locationA, locationB):
        return 10
    # Get how long tasks with a given taskID take to accomplish, once
    # the agent has arrived at the location.
    def duration(self, taskID):
        if taskID==1:
            return 20
        return 10

# For debugging purposes
T1 = Task(0, [(30,40),(80,90)], "kitchen", 0, "check-for-food")
T2 = Task(0, [(70,80)], "lab", 0, "check-for-pizza")
T3 = Task(2, [(40,50)], "CSE315", 0, "check-for-cookies")
T4 = Task(3, [(60,90)], "2nd-floor", 0, "check-for-tacos")
# T5 = Task(3, 80, "CSE546", 1, "demand-cookies")
# T6 = Task(2, 80, "benson-store", 0, "check-for-chips")

class Solver:

    # Create a new Solver object.
    #
    # worldmap: An object that is derived from World, and can be used
    # to check the distance between any two locations, and the
    # duration of any task. The World base class should be used only
    # for testing, and not in any real application.
    #
    # curTime: The current global time. See note about global times in
    # Task constructor.
    #
    # tasks: The initial tasks for the solver. Passing in a non-empty
    # list is the same as passing in an empty list, and then adding
    # the the tasks one by one through Solver.addTask().
    def __init__(self, worldmap=World(), curTime=0, tasks=[]):
        self.tasks = tasks
        self.world = worldmap
        self.globalTime = curTime
        self.solver = z3.Solver()

    # Add a new task to the solver.
    #
    # task: The task object to add to the solver.
    #
    # curTime: The current global time. See note about global time in
    # Task constructor.
    def addTask(self, task, curTime=-1):
        self.tasks.append(task)
        if curTime != -1:
            self.updateTime(curTime)

    # Remove a task from the solver because it has been accomplished.
    def finishTask(self, task):
        self.tasks.remove(task)

    # Update the current global time of the Solver. The client should
    # never have to call this directly. See note about global time in
    # Task constructor.
    def updateTime(self, curTime):
        amount = curTime - self.globalTime
        self.globalTime = curTime
        for task in tasks:
            # Move all tasks intervals up by the amount of time that
            # has passed.
            lastDeadline = None
            newIntervals = []
            for start, end in task.intervals:
                newIntervals.append(start - amount, end - amount)
                if lastDeadline == None or end > lastDeadline:
                    lastDeadline = end
            task.intervals = newIntervals
            if lastDeadline < self.world.duration(task.ID):
                # If we don't have enough time to accomplish the task
                # anymore, give up on it.
                print "Missed last interval for task " + task.name
                self.finishTask(task)

    # Extracts the best solution once all the hard-hard constraints
    # have been set up. Hard-hard constraints are all the constraints
    # besides that any task is actually accomplished.
    def extractSolution(self):
        if self.debugPrint:
            print "clauses are: " + str(self.solver)

        # The variables cooresponding ;to the hard tasks.
        hardClauses = [v[-1] for k,v in self.taskVars.items() if k.weight == 0]

        if self.debugPrint:
            print "hardClauses: " + str(hardClauses)

        # Find the solution which maximizes the number of hard tasks
        # we accomplish.
        hardSolution = self.maxSAT(self.solver, [(clause, 1) for clause in hardClauses])
        # All the hard tasks that are part of the solution we
        # found. For the final solution, we require that all these
        # tasks be accomplished, and we try to see how many soft tasks
        # we can fit in in addition.
        acceptedHards = [v[-1] for k,v in self.taskVars.items()\
                         if k.weight == 0 and hardSolution[k][-1]]
        # Add the acceptedHards to the solvers hard clauses so that
        # they are hard constraints from now on.
        self.solver.add(*acceptedHards)
        # Find the solution including soft tasks that includes all the
        # accepted hards, plus maximize the soft task weights.
        solution = self.maxSAT(self.solver, [(v[-1], k.weight) for k,v in self.taskVars.items()\
                                             if k.weight != 0])
        # Extract the path from the solution.
        path = self.getPath(solution)
        # Print it, since the repl printed version is inscrutiable.
        print "Found path " + str([str(task) for task in path])
        # Return the path.
        return path

    # Given a solution, extract an path, which is a list of
    # instructions for the agent. Task objects indicate the agent
    # should do that task, and integers indicate the agent should wait
    # that amount of time.
    def getPath(self, solution):
        path = []
        # For each time step, add the task that is accomplished at
        # that time step, if it exists.
        for t in range(len(self.tasks)):
            if solution["waitBefores"][t] != 0:
                path.append(solution["waitBefores"][t])
            for task in self.tasks:
                if solution[task][t]:
                    path.append(task)
        return path

    # Get the path (list of instructions) that best accomplishes the
    # tasks that the solver has.
    def solveTasks(self, startLoc="l0", curTime=-1, debugPrint=False):
        # Set the debugPrint variable to whatever we were passed, so
        # that all the functions we call know to debugPrint.
        self.debugPrint = debugPrint
        # Reset the z3 instance.
        self.solver.reset()
        # If we were passed a real curTime, update our deadlines.
        if curTime != -1:
            self.updateTime(curTime)
        # Set the start location to the one we were passed.
        self.startLoc = startLoc
        # Populate the self.taskVars variable.
        self.createVars()
        # Add constraints which say that tasks are accomplished at at
        # most one timestep, and that at any given timestep at most
        # one task is accomplished.
        self.addUniqueTaskStepConstraint()
        # Add the variables which control how long has passed at each
        # timestep.
        self.addTimeVars()
        # Add constraints tying each task variable to whether that
        # task has been accomplished at some time step, and tying
        # whether a task has been accomplished at some timestep to
        # whether that timestep takes place in time for the tasks
        # deadline.
        self.addTaskConstraints()
        # Add constraints that all tasks that are accomplished must be
        # 'compressed' into the initial timesteps. That is, if no task
        # is accomplished for some timestep, then all timesteps after
        # must also be empty.
        self.addStepCompressedConstraints()
        # Extract the solution and return it.
        return self.extractSolution()

    # Get the distance between two tasks. This is a thin wrapper
    # around the call to World, but handles the case where the tasks
    # are at the same location, and extracts their locations if they
    # arent.
    def taskDistance(self, task1, task2):
        if task1.location == task2.location:
            return 0
        else:
            return self.world.time(task1.location, task2.location)

    # Create the self.taskVar table.
    def createVars(self):
        # self.taskVars is a dictionary that maps tasks to a table of
        # their variables.
        self.taskVars = {}
        for task in self.tasks:
            # For each table, the entry at -1 is the variable that
            # cooresponds to whether or not the task got done at all.
            self.taskVars[task] = {-1:z3.Bool(str(task))}
            for t in range(len(self.tasks)):
                # For each timestep t, the entry at t is whether the
                # task got done at that timestep.
                taskVarName = str(task) + "@" + str(t)
                self.taskVars[task][t] = z3.Bool(taskVarName)
        if self.debugPrint:
            print "Created Task Variables: " + str(self.taskVars)

    # Add the constraint that there is at most one task accomplished
    # at any given timestep, and each task is accomplished at at most
    # one timestep.
    def addUniqueTaskStepConstraint(self):
        uniqueTaskStepConstraints = []

        # There is at most one task accomplished at any given
        # timestep.
        for t in range(len(self.tasks)):
            tasksLeft = list(self.tasks)
            while len(tasksLeft) > 0:
                task = tasksLeft.pop()
                for otherTask in tasksLeft:
                    uniqueTaskStepConstraints.append(Or(Not(self.taskVars[task][t]), \
                                                        Not(self.taskVars[otherTask][t])))

        # Each task is accomplished at at most one timestep.
        for task in self.tasks:
            timesLeft = range(len(self.tasks))
            while len(timesLeft) > 0:
                time = timesLeft.pop()
                for otherTime in timesLeft:
                    uniqueTaskStepConstraints.append(Or(Not(self.taskVars[task][time]),\
                                                        Not(self.taskVars[task][otherTime])))

        for constraint in uniqueTaskStepConstraints:
            self.solver.add(constraint)
        if self.debugPrint:
            print "Added unique task step contraints: " + str(uniqueTaskStepConstraints)

    # Add constraints tying each task variable to whether or not it
    # was accomplished at some time, and whether or not it was
    # accomplished at any given time to whether that time in time for
    # the deadline.
    def addTaskConstraints(self):
        htConstraints = []
        for task in self.tasks:
            # Aggregate the variables indicating this task got done at
            # a particular time.
            taskAtTimes = []
            for t in range(len(self.tasks)):
                intervalVars = []
                # Did we do the task in any of our intervals?
                for i, (start, end) in enumerate(task.intervals):
                    # Create a variable for getting done in the interval.
                    intervalVar = z3.Bool(str(task) + "@" + str(t) + "_for_" + str(i))
                    # The task must be contained within the interval.
                    htConstraints.append(Or(Not(intervalVar),\
                                            self.timeVars[t] >= start))
                    htConstraints.append(Or(Not(intervalVar),\
                                            self.timeVars[t] + self.world.duration(task.ID) <= end))
                    intervalVars.append(intervalVar)
                # For a task to get done at a particular time, that
                # time must be within one of our intervals.
                htConstraints.append(Or(Not(self.taskVars[task][t]),\
                                        *intervalVars))
                taskAtTimes.append(self.taskVars[task][t])
            # For a task to get done at all, it has to get done at
            # some time.
            htConstraints.append(Or(Not(self.taskVars[task][-1]),*taskAtTimes))
        for constraint in htConstraints:
            self.solver.add(constraint)

        if self.debugPrint:
            print "Added hard task constraints: " + str(htConstraints)

    # Constrain the solution so that for any time step, if no task
    # gets done during that step, then no task can be done any step
    # after. This makes sure that there aren't "holes" in the
    # schedule, and all the tasks are in the beginning if less tasks
    # are accomplished than there are timesteps.
    def addStepCompressedConstraints(self):
        self.noneVars = []
        clauses = []
        # None at the step has to be true unless some task is true at
        # the step.
        for i in range(len(self.tasks)):
            self.noneVars.append(z3.Bool("None@"+str(i)))
            clauses.append(Or(self.noneVars[i],\
                              *[varTable[i] for var, varTable in self.taskVars.items()]))

        # If none is true at the step, then no task can be
        # true. Together, these two sets of constraints make up
        # bi-implication between the none variable, and no tasks being
        # accomplished at this step.
        for t in range(len(self.tasks)):
            for taskVar, varTable in self.taskVars.items():
                clauses.append(Or(Not(self.noneVars[t]),\
                                  Not(varTable[t])))

        # If any none variable is true, then the one after it is
        # true. Because of transitivity, this means that all none
        # variables after it are true.
        for i in range(len(self.tasks)):
            for j in range(i+1, len(self.tasks)):
                clauses.append(Or(Not(self.noneVars[i]), self.noneVars[j]))

        for clause in clauses:
            if self.debugPrint:
                print "adding clause " + str(clause)
            self.solver.add(clause)

    # Add the variables cooresponding to how much time has passed at
    # each step.
    def addTimeVars(self):
        timeConstraints = []
        self.waitBefores = []
        # Create the wait before variables, which indicate, at each
        # time step t, how much time should be waited before starting
        # that time step. This value must be non-negative.
        for t in range(len(self.tasks)):
            self.waitBefores.append(z3.Int("waitBefore"+str(t)))
            self.solver.add(self.waitBefores[t] >= 0)
        if len(self.tasks) == 0:
            firstMoveTime = 0
        else:
            firstMoveTime = self.waitBefores[0]
        # The firstMoveTime is the time it takes to get to the first
        # location. Add a constraint for each location that could
        # possibly come first, that if it does come first, add the
        # time it takes to get to it to firstMoveTime
        for task in self.tasks:
            firstMoveTime += If(self.taskVars[task][0], self.world.time(self.startLoc, task.location), 0)
        # Set this expression equal to a new variable.
        firstVar = z3.Int("TimeToFirstNode")
        timeConstraints.append(firstVar == firstMoveTime)
        # Aggregate the time variables.
        self.timeVars = [firstVar]
        # For each time step, create a new time variable.
        for t in range(len(self.tasks) - 1):
            # Start with the time variable from the previous iteration.
            time = self.timeVars[t] + self.waitBefores[t+1]
            # This little while loop trick allows us to get every pair
            # of tasks.
            tasksLeft = list(self.tasks)
            while len(tasksLeft) > 0:
                task1 = tasksLeft.pop()
                for task2 in tasksLeft:
                    # If we traveled between these two tasks from this
                    # time step to the next, add the time taken to our
                    # time variable.
                    time += If(Or(And(self.taskVars[task1][t], self.taskVars[task2][t+1]), \
                                  And(self.taskVars[task2][t], self.taskVars[task1][t+1])),\
                               self.taskDistance(task1,task2), 0)
                # Add the time taken accomplishing a task at this step
                # to the time variable.
                time += If(self.taskVars[task1][t], self.world.duration(task1.ID), 0)
            # Create a new time variable that cooresponds to this expression.
            var = z3.Int("TimeVar" + str(t))
            timeConstraints.append(var == time)
            # Add it to our aggregate.
            self.timeVars.append(var)

        if self.debugPrint:
            print "Added time variables: " + str(self.timeVars)
        for constraint in timeConstraints:
            self.solver.add(constraint)
        if self.debugPrint:
            print "Added time constraints: " + str(timeConstraints)

    ## All hard clauses should have already been added to the solver.
    def maxSAT(self, solver, var_weight_pairs):
        # A classic argmax loop, holding on to our best cost and the
        # cooresponding solution.
        min_cost = None
        best_solution = None
        # The variables that keep us from trying a solution we've
        # already tried, or a subset of that solution.
        conflictVars = []
        # Get our first solver result, the solution if we don't need
        # to accomplish any of our weighted vars.
        next_solver_result = solver.check()
        while(next_solver_result == z3.sat):
            # The cost of this solution.
            cost = 0
            # Get the solvers model.
            model = solver.model()
            # For each soft variable that was set to false in the
            # current solution, incur a cost.
            for var, weight in var_weight_pairs:
                if self.debugPrint:
                    print "adding cost of " + str(var) + ": " + str(weight) + " * "\
                        + str(not z3.is_false(model[var]))
                if z3.is_false(model[var]):
                    cost += weight

            # Extract a solution object. We would just save the model,
            # but it turns out z3 models are invalidated when you next
            # run the solver.
            solution = self.modelToSolution(model)

            # If our new cost is the best cost we've seen so far,
            # update our best.
            if min_cost == None or cost < min_cost:
                min_cost = cost
                best_solution = solution

            if self.debugPrint:
                print "found solution: "
                self.printSolution(solution)
                print "with cost " + str(cost)

            # Create a fresh variable that blocks any future solution
            # that does not include at least one of the tasks that
            # were excluded from this solution. That statement may
            # take a bit of unpacking. Basically the idea is, if we
            # have some solution, then there exists no better solution
            # which only does a subset of the tasks which this
            # solution does. So, we block all solutions which don't
            # include at least one other task that this solution
            # doesn't have. I got the algorithm from this paper:
            # http://research.microsoft.com/en-US/peopleb/nbjorner/scss2014.pdf
            # The paper actually shows that another algorithm is more
            # efficient, but this one is simpler, so we use this one
            # until we hit a performance bottleneck with it.
            fresh_var_name = "block"
            interp = [v for v,w in var_weight_pairs \
                      if z3.is_false(model[v])]
            for v in interp:
                fresh_var_name += "_" + str(v)
            fresh_var = z3.Bool(fresh_var_name)
            # Tie our blocking constraint to a new "conflict
            # variable," and add that variable to our set of
            # assumptions.
            block_constraint = Or(Not(fresh_var), *interp)
            if self.debugPrint:
                print "adding block constraint " + str(block_constraint)
            solver.add(block_constraint)
            conflictVars.append(fresh_var)
            # Get a new result for the next time around the while loop.
            next_solver_result = solver.check(*conflictVars)
        if self.debugPrint:
            print "best solution was "
            self.printSolution(best_solution)
            print "with cost " + str(min_cost)
        return best_solution

    # Convert a model to a solution object.
    def modelToSolution(self, solverModel):
        solution = {}
        # Build a structure parallel to self.taskVars, which instead
        # of each variable holds the current mapping of that variable.
        for key, varTable in self.taskVars.items():
            solution[key] = {}
            for index, var in varTable.items():
                solution[key][index] = z3.is_true(solverModel[var])
        solution["waitBefores"] = {}
        for t in range(len(self.tasks)):
            solution["waitBefores"][t] = solverModel[self.waitBefores[t]].as_long()
        return solution

    # Print the solution object, by printing all the bindings that it
    # contains.
    def printSolution(self, solution):
        for key, varTable in self.taskVars.items():
            for index, var in varTable.items():
                print str(var) + ": " + str(solution[key][index])
