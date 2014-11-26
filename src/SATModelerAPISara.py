#!/usr/bin/env python
import roslib
roslib.load_manifest('rospy')

import rospy
import rospkg
import csv
from sat_schedule_solver.srv import (
    SAT_Scheduler,
    SAT_SchedulerRequest,
    ScheduleAllQueryJobs,
    ScheduleAllQueryJobsResponse
)

import time

class SATModelerAPISara():
    def __init__(self):
        rospy.init_node('SATModelerAPISara', anonymous=True)
        rospy.wait_for_service('/SAT_Scheduler')
        srvModeler = rospy.Service('/sat_scheduler_API',
                                   ScheduleAllQueryJobs,
                                   self.handleDBJobUpdateRequest)
        self.SAT_Scheduler_Service = rospy.ServiceProxy('/SAT_Scheduler', SAT_Scheduler)
        self.sequence = 0
        self.run()
    
    def handleDBJobUpdateRequest(self, req):
        resp = ScheduleAllQueryJobsResponse()
        resp.header = req.header
        resp.success = True
        return resp
    
    def run(self):
        count = 0
        outMsg = SAT_SchedulerRequest()
        outMsg.header.seq = self.sequence
        outMsg.header.stamp = rospy.Time.now()
        outMsg.header.frame_id = "/SAT/Scheduler/Input"
        
        self.sequence += 1
        jobIDsList = []
        startTimesList = []
        endTimesList = []
        prioritiesList = []
        
        outMsg.numConstraints = count
        outMsg.jobID = jobIDsList
        outMsg.startTimes = startTimesList
        outMsg.endTimes = endTimesList
        outMsg.priority = prioritiesList
        
        sequence += 1
    
    def confirmResult(self, resp):
        print "SAT_Scheduler Response"
        print "  header:"
        print "    seq = " + str(resp.header.seq)
        print "    stamp = " + str(resp.header.stamp)
        print "    sframe_id = " + str(resp.header.frame_id)
        
        print "  numJobsAccepted  = " + str(resp.numJobsAccepted)
        print "  acceptedJobID  = " + str(resp.acceptedJobID)
        print "  jobEndTime  = " + str(resp.jobEndTime)
        
if __name__ == '__main__':
    rospack = rospkg.RosPack()
    apiDriver = SATModelerAPISara()
    