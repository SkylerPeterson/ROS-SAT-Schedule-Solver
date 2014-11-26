#!/usr/bin/env python
import roslib
roslib.load_manifest('rospy')

import rospy
import rospkg
import csv
from sat_schedule_solver.srv import (
    SAT_Scheduler,
    SAT_SchedulerRequest
)

import time

class SATModelerAPISara():
    def __init__(self):
        rospy.init_node('SATModelerAPISara', anonymous=True)
        rospy.wait_for_service('/SAT_Scheduler')
        self.SAT_Scheduler_Service = rospy.ServiceProxy('/SAT_Scheduler', SAT_Scheduler)
        self.sequence = 0
    
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
    
