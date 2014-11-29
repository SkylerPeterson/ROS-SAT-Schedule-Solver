## Encoder.py
## Takes a list of Tasks, and returns whether or not the tasks can be completed, given a WorldMap

import z3
from z3 import Not, Or, And, If

class Task:
    def __init__(self, weight, deadline, location, duration, name):
        if weight != 0:
            raise NotImplementedError()
        self.weight = weight
        self.deadline = deadline
        self.location = location
        self.duration = duration
        self.name = name

    def __str__(self):
        return self.name

class WorldMap:
    def time(self, locationA, locationB):
        return 10

class Solver:
    START = Task(0,0,"",0,"Start")
    
    def __init__(self, worldmap=WorldMap(), curTime=0, tasks=[]):
        self.tasks = tasks
        self.world = worldmap
        self.globalTime = curTime
        self.solver = z3.Solver()

    def addTask(self, task, curTime=-1):
        if curTime != -1:
            self.updateTime(curTime)
        self.tasks.append(task)

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
            if task.deadline < task.duration:
                print "Missed deadline for task " + task.name
                self.giveUpTask(task)

    def solveTasks(self, startLoc="l0", curTime=-1, debugPrint=False):
        self.debugPrint = debugPrint
        self.solver.reset()
        if curTime != -1:
            self.updateTime(curTime)
        self.startLoc = startLoc
        self.addVars()
        self.addUniqueTaskStepConstraint()
        self.addTimeVars()
        self.addHardTaskConstraints()
        if self.solver.check(*[v[-1] for k,v in self.taskVars.items()]) == z3.sat:
            model = self.solver.model()
            path = []
            if self.debugPrint:
                print(model)
            for t in range(len(self.tasks)):
                for task in self.tasks:
                    if z3.is_true(model[self.taskVars[task][t]]):
                        path.append(task)

            print "found path " + str([str(task) for task in path])
            return path
        else:
            print "Could not find a valid path!"
            unsatCore = self.solver.unsat_core()
            unsatCoreTasks = [task for task in self.tasks if self.taskVars[task][-1] in unsatCore]
            # Heuristic for the task most likely to allow a path if it is removed
            removeTask = max(unsatCoreTasks, key=lambda task: task.duration / task.deadline)
            self.giveUpTask(removeTask)
            return self.solveTasks(startLoc,curTime,debugPrint)

    def taskDistance(self, task1, task2):
        if task1.location == task2.location:
            return 0
        elif task1 == Solver.START:
            return self.world.time(self.startLoc, task2.location)
        elif task2 == Solver.START:
            return self.world.time(self.startLoc, task1.location)
        else:
            return self.world.time(task1.location, task2.location)

    def addVars(self):
        self.taskVars = {}
        for task in self.tasks:
            self.taskVars[task] = {-1:z3.Bool(str(task))}
            for t in range(len(self.tasks)):
                taskName = str(task) + "@" + str(t)
                self.taskVars[task][t] = z3.Bool(taskName)
        if self.debugPrint:
            print "Created Task Variables: " + str(self.taskVars)

    def addUniqueTaskStepConstraint(self):
        uniqueTaskStepConstraints = []
        for t in range(len(self.tasks)):
            tasksLeft = list(self.tasks)
            while len(tasksLeft) > 0:
                task = tasksLeft.pop()
                for otherTask in tasksLeft:
                    uniqueTaskStepConstraints.append(Or(Not(self.taskVars[task][t]), Not(self.taskVars[otherTask][t])))
        for constraint in uniqueTaskStepConstraints:
            self.solver.add(constraint)
        if self.debugPrint:
            print "Added unique task step contraints: " + str(uniqueTaskStepConstraints)

    def addHardTaskConstraints(self):
        htConstraints = []
        for task in self.tasks:
            if task.weight == 0:
                taskAtTimes = []
                for t in range(len(self.tasks)):
                    htConstraints.append(Or(Not(self.taskVars[task][t]), self.timeVars[t] + task.duration <= task.deadline))
                    taskAtTimes.append(self.taskVars[task][t])
                htConstraints.append(Or(Not(self.taskVars[task][-1]),*taskAtTimes))
        for constraint in htConstraints:
            self.solver.add(constraint)

        if self.debugPrint:
            print "Added hard task constraints: " + str(htConstraints)

    def addTimeVars(self):
        timeConstraints = []
        firstMoveTime = 0
        for task in self.tasks:
            firstMoveTime += If(self.taskVars[task][0], self.taskDistance(Solver.START, task), 0)
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
                time += If(self.taskVars[task1][t], task1.duration, 0)
            var = z3.Int("TimeVar" + str(t))
            timeConstraints.append(var == time)
            self.timeVars.append(var)
        if self.debugPrint:
            print "Added time variables: " + str(self.timeVars)
        for constraint in timeConstraints:
            self.solver.add(constraint)
        if self.debugPrint:
            print "Added time constraints: " + str(timeConstraints)
