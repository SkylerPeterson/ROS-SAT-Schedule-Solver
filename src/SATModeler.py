#!/usr/bin/env python
import roslib
roslib.load_manifest('rospy')

import rospy
from encoder import Solver, Task
from datetime import datetime
from calendar import isleap
from pytz import utc
from math import floor, ceil
from sat_schedule_solver.srv import (
    SAT_Scheduler,
    SAT_SchedulerResponse
)

class SATModeler():
    def __init__(self):
        rospy.init_node('SATModeler', anonymous=True)
        srvModeler = rospy.Service("/SAT_Scheduler",
                                   SAT_Scheduler,
                                   self.handleSchedulerRequest)
        print "SATModeler is running"
        rospy.spin()
        
    def handleSchedulerRequest(self, req):
        print req
        if (req.numConstraints != len(req.jobID)):
            rospy.logerr("Number of constraints and job IDs does not match.")
        if (req.numConstraints != len(req.startTimes)):
            rospy.logerr("Number of constraints and start times does not match.")
        if (req.numConstraints != len(req.endTimes)):
            rospy.logerr("Number of constraints and end times does not match.")
        if (req.numConstraints != len(req.priority)):
            rospy.logerr("Number of constraints and priorities does not match.")
        if (req.numConstraints != len(req.location)):
            rospy.logerr("Number of constraints and locations does not match.")
        if (req.numConstraints != len(req.taskId)):
            rospy.logerr("Number of constraints and task IDs does not match.")
        
        now = datetime.utcnow().replace(tzinfo=utc)
        tasks = []
        for i in range(0, req.numConstraints):
            deadline = readDatetimeMsg(req.endTimes[i])
            tasks.append(Task(req.priority[i], (deadline - now).total_seconds(), req.location[i], req.taskId[i], req.jobID[i]))
        #TODO: Add World object to get travel times and task durations.
        solver = Solver(tasks=tasks)
        taskList = solver.solveTasks()
        
        resp = SAT_SchedulerResponse()
        resp.header.seq = req.header.seq
        resp.header.stamp = rospy.Time.now()
        resp.header.frame_id = "/SAT/Scheduler/Output"
        resp.numJobsAccepted = len(taskList)
        for i in range(0, resp.numJobsAccepted):
            resp.acceptedJobID.append(taskList[i].name)
            resp.jobEndTime.append(addTimes(datetime.utcfromtimestamp(taskList[i].deadline), now))
        return resp

def readDatetimeMsg(dtMsg):
    return datetime(dtMsg.year, dtMsg.month, dtMsg.day, dtMsg.hour, dtMsg.minute, dtMsg.second, dtMsg.microsecond, utc)

def addTimes(time1, time2):
    year = time1.year + time2.year - 1970
    month = time1.month + time2.month - 1
    if month > 12:
        month -= 12
        year += 1
    day = time1.day + time2.day - 1
    if (month in (1,3,5,7,8,10,12)) and day > 31:
        day -= 31
        month += 1
    elif (month in (4,6,9,11)) and day > 30:
        day -= 30
        month += 1
    elif (month == 2):
        if isleap(year) and day > 29:
            day -= 29
            month += 1
        if (not isleap(year)) and day > 28:
            day -= 28
            month += 1
    hour = time1.hour + time2.hour
    if (hour >= 24):
        hour -= 24
        day += 1
    minute = time1.minute + time2.minute
    if (minute >= 60):
        minute -= 60
        hour += 1
    second = time1.second + time2.second
    if (second >= 60):
        second -= 60
        minute += 1
    microsecond = time1.microsecond + time2.microsecond
    if (microsecond >= 1000000):
        microsecond -= 1000000
        second += 1
    return datetime(year, month, day, hour, minute, second, microsecond, utc)

if __name__ == '__main__':
    SATModeler()
