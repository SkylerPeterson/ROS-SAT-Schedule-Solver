#!/usr/bin/env python

import roslib
roslib.load_manifest('rospy')

import rospy

class SATModeler():

    def __init__(self):
        rospy.init_node('SATModeler', anonymous=True)
        pubModel = rospy.Publisher('SAT_Schedule_Model', SAT_Model, queue_size=10)
        
        # Input message handlers
        # TODO: Add subscribers as we learn them
        # rospy.Subscriber('pubName', MessageName, self.callbackfunc)
        
