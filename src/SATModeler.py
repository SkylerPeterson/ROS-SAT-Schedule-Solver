#!/usr/bin/env python
import roslib
roslib.load_manifest('rospy')

import rospy
from encoder import Solver, Task
from datetime import datetime
from pytz import utc
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
        req.header.seq
        req.header.stamp
        req.header.frame_id
        req.numConstraints
        req.jobID
        req.startTimes
        req.endTimes
        req.priority
        req.location
        
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
        
        #TODO: Need to add actual job duration function
        now = datetime.utcnow().replace(tzinfo=utc)
        tasks = []
        for i in range(0, req.numConstraints):
            deadline = readDatetimeMsg(req.endTimes[i])
            duration = 10
            tasks.append(Task(req.priority[i], (deadline - now).total_seconds(), req.location[i], duration, req.jobID[i]))
        solver = Solver(curTime=now, tasks=tasks)
        solver.solveTasks()
        #TODO: Create response from solver response
        resp = SAT_SchedulerResponse()
        resp.header = req.header
        resp.numJobsAccepted = req.numConstraints
        resp.acceptedJobID = req.jobID
        resp.jobEndTime = req.endTimes
        return resp
        
def readDatetimeMsg(dtMsg):
    return datetime(dtMsg.year, dtMsg.month, dtMsg.day, dtMsg.hour, dtMsg.minute, dtMsg.second, dtMsg.microsecond, utc)
        
if __name__ == '__main__':
    SATModeler()
