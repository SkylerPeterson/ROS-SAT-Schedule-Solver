#!/usr/bin/env python
import roslib
roslib.load_manifest('rospy')

import rospy
import csv
from sat_schedule_solver.msg import *

class SATModelerAPITest():

    def __init__(self):
        pubModel = rospy.Publisher('SAT_Schedule_Model', SAT_Model, queue_size=10)
        rospy.init_node('SATModelerAPITest', anonymous=True)
        
        # Input message handlers
        rospy.Subscriber('SAT_Schedule_Solution', SAT_Solution, self.confirmResult)
    
    def runTest(self, fileName):
        with open(fileName, 'rb') as csvfile:
            filereader = csv.reader(csvfile, delimiter=',')
            for row in filereader:
                print ', '.join(row)
    
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
    testDriver = SATModelerAPITest()
    testDriver.runTest("/home/skyler/Dropbox/CSE507/Project/catkin_indigo_ws/src/sat_schedule_solver/testFiles/Test1.txt")
