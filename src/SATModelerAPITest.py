#!/usr/bin/env python
import roslib
roslib.load_manifest('rospy')

import rospy
import rospkg
import csv
from sat_schedule_solver.msg import *

import time

class SATModelerAPITest():

    NUM_COLUMNS = 6

    def __init__(self):
        self.sequence = 0
        self.modelPub = rospy.Publisher('SAT_Schedule_Model', SAT_Model, queue_size=10)
        rospy.init_node('SATModelerAPITest', anonymous=True)
        
        # Input message handlers
        rospy.Subscriber('SAT_Schedule_Solution', SAT_Solution, self.confirmResult)
    
    def runTest(self, fileName):
        count = 0
        outMsg = SAT_Model()
        outMsg.header.seq = self.sequence
        outMsg.header.stamp = rospy.Time.now()
        outMsg.header.frame_id = "Schedule/Input"
        
        self.sequence += 1
        jobIDsList = []
        startTimesList = []
        endTimesList = []
        prioritiesList = []
        with open(fileName, 'rb') as csvfile:
            filereader = csv.reader(csvfile, delimiter=',')
            for row in filereader:
                if (len(row) != self.NUM_COLUMNS):
                    print "File incorrectly formatted."
                    exit()
                count += 1
                jobIDsList.append(row[0])
                startTimesList.append(rospy.Time(int(row[1]), int(row[2])))
                endTimesList.append(rospy.Time(int(row[3]), int(row[4])))
                prioritiesList.append(int(row[5]))
        
        outMsg.numConstraints = count
        outMsg.jobID = jobIDsList
        outMsg.startTimes = startTimesList
        outMsg.endTimes = endTimesList
        outMsg.priority = prioritiesList
        
        self.modelPub.publish(outMsg)
    
    def confirmResult(self, msg):
        #sequence ID: consecutively increasing ID
        msg.header.seq
        #Two-integer timestamp that is expressed as:
        # * stamp.secs: seconds (stamp_secs) since epoch
        # * stamp.nsecs: nanoseconds since stamp_secs
        # time-handling sugar is provided by the client library
        msg.header.stamp
        #Frame this data is associated with
        msg.header.sframe_id
        
        #Number of constraints, size of following arrays
        msg.numConstraints
        #List of job IDs as uints
        msg.startTimes
        #List of start times in ROS time
        msg.startTimes
        #List of end times in ROS time
        msg.endTimes
        #List of uint priorities
        msg.priority
        
if __name__ == '__main__':
    rospack = rospkg.RosPack()
    testDriver = SATModelerAPITest()
    testDriver.runTest(rospack.get_path('sat_schedule_solver') + "/testFiles/Test1.txt")
