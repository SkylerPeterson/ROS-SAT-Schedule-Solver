#!/usr/bin/env python
import roslib
roslib.load_manifest('rospy')

import rospy
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
        req.header.seq
        req.header.stamp
        req.header.frame_id
        req.numConstraints
        req.jobID
        req.startTimes
        req.endTimes
        req.priority
        
        # We will at some point generate an actual response.
        # Just echo to test for now.
        resp = SAT_SchedulerResponse()
        resp.header = req.header
        resp.numJobsAccepted = req.numConstraints
        resp.acceptedJobID = req.jobID
        resp.jobEndTime = req.endTimes
        return resp
        
if __name__ == '__main__':
    SATModeler()
