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
    SAT_SchedulerResponse,
    SAT_World_Map_Duration,
    SAT_World_Map_Time
)

class SATModeler():
    def __init__(self):
        rospy.init_node('SATModeler', anonymous=True)
        srvModeler = rospy.Service("/SAT_Scheduler",
                                   SAT_Scheduler,
                                   self.handleSchedulerRequest)
        self.worldmapservice = ServiceWorldMap()
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
        tasks = dict()
        for i in range(0, req.numConstraints):
            baseline = readDatetimeMsg(req.startTimes[i])
            deadline = readDatetimeMsg(req.endTimes[i])
            interval = [((baseline - now).total_seconds(), (deadline - now).total_seconds())]
            if req.jobID[i] not in tasks:
                tasks[req.jobID[i]] = Task(req.priority[i], interval, req.location[i], req.taskId[i], req.jobID[i])
            else:
                task = tasks[req.jobID[i]]
                task.intervals.append(interval)
                if task.weight != req.priority[i]:
                    rospy.logerr("Task contains multiple priorities: %d and %d.", task.weight, req.priority[i])
                if task.location != req.location[i]:
                    rospy.logerr("Task contains multiple locations: %s and %s.", task.location, req.location[i])
                if task.taskID != req.taskId[i]:
                    rospy.logerr("Task contains multiple task Ids: %d and %d.", task.taskID, req.taskId[i])
        solver = Solver(worldmap=self.worldmapservice, tasks=tasks.values())
        taskList = solver.solveTasks(startLoc="startPos")
        
        resp = SAT_SchedulerResponse()
        resp.header.seq = req.header.seq
        resp.header.stamp = rospy.Time.now()
        resp.header.frame_id = "/SAT/Scheduler/Output"
        resp.numJobsAccepted = len(taskList)
        prevLocation = 'startPos'
        for i in range(0, resp.numJobsAccepted):
            if isinstance(taskList[i], ( int, long )):
                resp.acceptedJobID.append("wait")
                resp.jobEndTime.append(addTimes(datetime.utcfromtimestamp(taskList[i]), now))
            elif isinstance(taskList[i], Task):
                resp.acceptedJobID.append(taskList[i].name)
                taskTime = self.worldmapservice.time(prevLocation, taskList[i].location) + self.worldmapservice.duration(taskList[i].ID)
                resp.jobEndTime.append(addTimes(datetime.utcfromtimestamp(taskTime), now))
                prevLocation = taskList[i].location
            else:
                rospy.logerr("Result from encoder includes unsuported type.")
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


class ServiceWorldMap():
    def __init__(self):
        #rospy.init_node('SATServiceBasedWorldMap', anonymous=True)
        # Setup services and messages
        rospy.wait_for_service('/SAT_World_Map_Time')
        self.SAT_World_Time = rospy.ServiceProxy('/SAT_World_Map_Time', SAT_World_Map_Time)
        rospy.wait_for_service('/SAT_World_Map_Duration')
        self.SAT_World_Duration = rospy.ServiceProxy('/SAT_World_Map_Duration', SAT_World_Map_Duration)
        print "SATWorldMap is running"
    
    def time(self, locationA, locationB):
        try:
            resp = self.SAT_World_Time(locationA, locationB)
        except rospy.ServiceException, e:
            print "Service call failed: %s"%e
        return resp.time
    
    def duration(self, taskID):
        try:
            resp = self.SAT_World_Duration(taskID)
        except rospy.ServiceException, e:
            print "Service call failed: %s"%e
        return resp.time

if __name__ == '__main__':
    SATModeler()
