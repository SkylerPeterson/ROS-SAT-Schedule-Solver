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

class SATModelerAPITest():

    NUM_COLUMNS = 6

    def __init__(self):
        rospy.init_node('SATModelerAPITest', anonymous=True)
        rospy.wait_for_service('/SAT_Scheduler')
        self.SAT_Scheduler_Service = rospy.ServiceProxy('/SAT_Scheduler', SAT_Scheduler)
        self.sequence = 0
    
    def runTest(self, fileName):
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
        with open(fileName, 'rb') as csvfile:
            filereader = csv.reader(csvfile, delimiter=',')
            for row in filereader:
                if (len(row[2:])%4 != 0):
                    print "File incorrectly formatted."
                    exit()
                count += 1
                for i in range(2, len(row), 4):
                    jobIDsList.append(row[0])
                    prioritiesList.append(int(row[1]))
                    startTimesList.append(rospy.Time(int(row[i]), int(row[i+1])))
                    endTimesList.append(rospy.Time(int(row[i+2]), int(row[i+3])))
        
        outMsg.numConstraints = count
        outMsg.jobID = jobIDsList
        outMsg.startTimes = startTimesList
        outMsg.endTimes = endTimesList
        outMsg.priority = prioritiesList
        
        try:
            SAT_Resp = self.SAT_Scheduler_Service(outMsg)
            self.confirmResult(SAT_Resp)
        except rospy.ServiceException, e:
            print "Service call failed: %s"%e
    
    def confirmResult(self, resp):
        print "SAT_Scheduler Response"
        print "  header.seq = " + str(resp.header.seq)
        print "  header.stamp = " + str(resp.header.stamp)
        print "  header.sframe_id = " + str(resp.header.frame_id)
        
        print " numJobsAccepted  = " + str(resp.numJobsAccepted)
        print " acceptedJobID  = " + str(resp.acceptedJobID)
        print " jobEndTime  = " + str(resp.jobEndTime)
        
if __name__ == '__main__':
    rospack = rospkg.RosPack()
    testDriver = SATModelerAPITest()
    testDriver.runTest(rospack.get_path('sat_schedule_solver') + "/testFiles/Test1.txt")
