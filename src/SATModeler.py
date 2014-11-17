#!/usr/bin/env python
import roslib
roslib.load_manifest('rospy')

import rospy
from sat_schedule_solver.msg import *

class SATModeler():

    def __init__(self):
        rospy.init_node('SATModeler', anonymous=True)
        pubModel = rospy.Publisher('SAT_Schedule_Solution', SAT_Solution, queue_size=10)
        
        # Input message handlers
        rospy.Subscriber('SAT_Schedule_Model', SAT_Model, self.runModeler)
        
    def runModeler(self, msg):
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
