## Encoder.py
## Takes a list of Tasks, and returns whether or not the tasks can be completed, given a World

import z3
from z3 import Not, Or, And, If

class Task:
    def __init__(self, weight, deadline, location, taskID, name):
        self.weight = weight
        self.deadline = deadline
        self.location = location
        self.ID = taskID
        self.name = name

    def __str__(self):
        return self.name

class World:
    def time(self, locationA, locationB):
        return 10
    def duration(self, taskID):
        return 10

# For debugging purposes
T1 = Task(0, 20, "kitchen", 0, "check-for-food")
T2 = Task(0, 30, "lab", 0, "check-for-pizza")
T3 = Task(0, 40, "CSE315", 0, "check-for-cookies")
T4 = Task(2, 60, "2nd-floor", 0, "check-for-tacos")
T5 = Task(3, 80, "CSE546", 1, "demand-cookies")
T6 = Task(2, 80, "benson-store", 0, "check-for-chips")

class Solver:
    def __init__(self, worldmap=World(), curTime=0, tasks=[]):
        self.tasks = tasks
        self.world = worldmap
        self.globalTime = curTime
        self.solver = z3.Solver()

    def addTask(self, task, curTime=-1):
        self.tasks.append(task)
        if curTime != -1:
            self.updateTime(curTime)

    def finishTask(self, task):
        self.tasks.remove(task)

    def giveUpTask(self, task):
        print "Giving up on task " + task.name
        self.finishTask(task)

    def updateTime(self, curTime):
        amount = curTime - self.globalTime
        self.globalTime = curTime
        for task in tasks:
            task.deadline -= amount
            if task.deadline < self.world.duration(task.ID):
                print "Missed deadline for task " + task.name
                self.giveUpTask(task)

    def extractSolution(self):
        if self.debugPrint:
            print "clauses are: " + str(self.solver)
        hardClauses = [v[-1] for k,v in self.taskVars.items() if k.weight == 0]
        if self.debugPrint:
            print "hardClauses: " + str(hardClauses)
        hardSolution = self.maxSAT(self.solver, [(clause, 1) for clause in hardClauses])
        acceptedHards = [v[-1] for k,v in self.taskVars.items()\
                         if k.weight == 0 and hardSolution[k][-1]]
        self.solver.add(*acceptedHards)
        solution = self.maxSAT(self.solver, [(v[-1], k.weight) for k,v in self.taskVars.items()\
                                             if k.weight != 0])
        path = self.getPath(solution)
        print "Found path " + str([str(task) for task in path])
        return path

    def getPath(self, solution):
        path = []
        for t in range(len(self.tasks)):
            for task in self.tasks:
                if solution[task][t]:
                    path.append(task)
        return path

    def solveTasks(self, startLoc="l0", curTime=-1, debugPrint=False):
        self.debugPrint = debugPrint
        self.solver.reset()
        if curTime != -1:
            self.updateTime(curTime)
        self.startLoc = startLoc
        self.createVars()
        self.addUniqueTaskStepConstraint()
        self.addTimeVars()
        self.addTaskConstraints()
        return self.extractSolution()

    def taskDistance(self, task1, task2):
        if task1.location == task2.location:
            return 0
        else:
            return self.world.time(task1.location, task2.location)

    def createVars(self):
        self.taskVars = {}
        for task in self.tasks:
            self.taskVars[task] = {-1:z3.Bool(str(task))}
            for t in range(len(self.tasks)):
                taskVarName = str(task) + "@" + str(t)
                self.taskVars[task][t] = z3.Bool(taskVarName)
        if self.debugPrint:
            print "Created Task Variables: " + str(self.taskVars)

    def addUniqueTaskStepConstraint(self):
        uniqueTaskStepConstraints = []
        for t in range(len(self.tasks)):
            tasksLeft = list(self.tasks)
            while len(tasksLeft) > 0:
                task = tasksLeft.pop()
                for otherTask in tasksLeft:
                    uniqueTaskStepConstraints.append(Or(Not(self.taskVars[task][t]), \
                                                        Not(self.taskVars[otherTask][t])))
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

    def addTaskConstraints(self):
        htConstraints = []
        for task in self.tasks:
            taskAtTimes = []
            for t in range(len(self.tasks)):
                htConstraints.append(Or(Not(self.taskVars[task][t]), \
                                        self.timeVars[t] + self.world.duration(task.ID) <= task.deadline))
                taskAtTimes.append(self.taskVars[task][t])
            htConstraints.append(Or(Not(self.taskVars[task][-1]),*taskAtTimes))
        for constraint in htConstraints:
            self.solver.add(constraint)

        if self.debugPrint:
            print "Added hard task constraints: " + str(htConstraints)

    def addStepCompressedConstraints(self):
        self.noneVars = []
        clauses = []
        for i in range(len(self.tasks)):
            self.noneVars.append(z3.Bool("None@"+str(i)))
            clauses.append(Or(self.noneVars[i],\
                              *[varTable[i] for var, varTable in self.taskVars.items()]))
        for t in range(len(self.tasks)):
            for taskVar, varTable in self.taskVars.items():
                clauses.append(Or(Not(self.noneVars[t]),\
                                  Not(varTable[t])))
        for i in range(len(self.tasks)):
            for j in range(i+1, len(self.tasks)):
                clauses.append(Or(Not(self.noneVars[i]), self.noneVars[j]))
        for clause in clauses:
            if self.debugPrint:
                print "adding clause " + str(clause)
            self.solver.add(clause)

    def addTimeVars(self):
        timeConstraints = []
        firstMoveTime = 0
        for task in self.tasks:
            firstMoveTime += If(self.taskVars[task][0], self.world.time(self.startLoc, task.location), 0)
        firstVar = z3.Int("TimeToFirstNode")
        timeConstraints.append(firstVar == firstMoveTime)
        self.timeVars = [firstVar]
        for t in range(len(self.tasks) - 1):
            time = self.timeVars[t]
            tasksLeft = self.tasks[:]
            while len(tasksLeft) > 0:
                task1 = tasksLeft.pop()
                for task2 in tasksLeft:
                    time += If(Or(And(self.taskVars[task1][t], self.taskVars[task2][t+1]), \
                                  And(self.taskVars[task2][t], self.taskVars[task1][t+1])),\
                               self.taskDistance(task1,task2), 0)
                time += If(self.taskVars[task1][t], self.world.duration(task1.ID), 0)
            var = z3.Int("TimeVar" + str(t))
            timeConstraints.append(var == time)
            self.timeVars.append(var)
        if self.debugPrint:
            print "Added time variables: " + str(self.timeVars)
        for constraint in timeConstraints:
            self.solver.add(constraint)
        if self.debugPrint:
            print "Added time constraints: " + str(timeConstraints)

    ## All hard clauses should have already been added to the solver.
    def maxSAT(self, solver, var_weight_pairs):
        min_cost = None
        best_solution = None
        conflictVars = []
        next_solver_result = solver.check(*conflictVars)
        while(next_solver_result == z3.sat):
            cost = 0
            model = solver.model()
            for var, weight in var_weight_pairs:
                if self.debugPrint:
                    print "adding cost of " + str(var) + ": " + str(weight) + " * "\
                        + str(not z3.is_false(model[var]))
                if z3.is_false(model[var]):
                    cost += weight
            solution = self.modelToSolution(model)

            if min_cost == None or cost < min_cost:
                min_cost = cost
                best_solution = solution

            if self.debugPrint:
                print "found solution: "
                self.printSolution(solution)
                print "with cost " + str(cost)

            fresh_var_name = "block"
            interp = [v for v,w in var_weight_pairs \
                      if z3.is_false(model[v])]
            for v in interp:
                fresh_var_name += "_" + str(v)
            fresh_var = z3.Bool(fresh_var_name)
            block_constraint = Or(Not(fresh_var), *interp)
            if self.debugPrint:
                print "adding block constraint " + str(block_constraint)
            solver.add(block_constraint)
            conflictVars.append(fresh_var)
            next_solver_result = solver.check(*conflictVars)
        if self.debugPrint:
            print "best solution was "
            self.printSolution(best_solution)
            print "with cost " + str(min_cost)
        return best_solution

    def modelToSolution(self, solverModel):
        solution = {}
        for key, varTable in self.taskVars.items():
            solution[key] = {}
            for index, var in varTable.items():
                solution[key][index] = z3.is_true(solverModel[var])
        solution["None"]={}
        for t in range(len(self.noneVars)):
            solution["None"][t] = not z3.is_false(solverModel[self.noneVars[t]])
        return solution

    def printSolution(self, solution):
        for key, varTable in self.taskVars.items():
            for index, var in varTable.items():
                print str(var) + ": " + str(solution[key][index])
        for t in range(len(self.noneVars)):
            print "None" + str(t) + ": " + str(solution["None"][t])
