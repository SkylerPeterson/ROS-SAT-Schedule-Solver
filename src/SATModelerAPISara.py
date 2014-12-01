#!/usr/bin/env python
import roslib
roslib.load_manifest('rospy')

import rospy
import rospkg
from sat_schedule_solver.srv import (
    SAT_Scheduler,
    SAT_SchedulerRequest,
    ScheduleAllQueryJobs,
    ScheduleAllQueryJobsResponse
)
from sat_schedule_solver.msg import (
    datetimemsg
)
from sara_queryjob_manager.msg import (
    QueryJobStatus, QueryJobUpdate
)
from datetime import datetime
from time import time, mktime
from pytz import utc
from pymongo import MongoClient
import csv
import sys

RECEIVED = QueryJobStatus.RECEIVED
SCHEDULED = QueryJobStatus.SCHEDULED
RUNNING = QueryJobStatus.RUNNING
SUCCEEDED = QueryJobStatus.SUCCEEDED
CANCELLED = QueryJobStatus.CANCELLED
FAILED = QueryJobStatus.FAILED
ABORTED = QueryJobStatus.ABORTED

class SATModelerAPISara():
    def __init__(self):
        rospy.init_node('SATModelerAPISara', anonymous=True)
        # Connect to DB.
        dbname = rospy.get_param("~dbname", "sara_uw_website")
        collname = rospy.get_param("~collname", "queryjobs")
        connection = MongoClient()
        self._collection = connection[dbname][collname]
        # Setup services and messages
        rospy.wait_for_service('/SAT_Scheduler')
        self.SAT_Scheduler_Service = rospy.ServiceProxy('/SAT_Scheduler', SAT_Scheduler)
        srvModeler = rospy.Service('/sat_scheduler_API',
                                   ScheduleAllQueryJobs,
                                   self.handleDBJobUpdateRequest)
        self._pub = rospy.Publisher('/queryjob_update', QueryJobUpdate, queue_size=10000)
        # Initialize variables
        self.sequence = 0
        print "SATModelerAPISara is running"
        rospy.spin()
    
    def handleDBJobUpdateRequest(self, req):
        resp = ScheduleAllQueryJobsResponse()
        resp.header = req.header
        try:
            jobList = self.getAllJobsFromDB()
            acceptedJobs, cancelledJobs = self.scheduleJobs(jobList)
            self.publishUpdates(acceptedJobs, cancelledJobs)
            resp.success = True
        except:
            rospy.logerr("Error while scheduling results:", sys.exc_info()[0])
            resp.success = False
        
        return resp
        
    def publishUpdates(self, acceptedJobList, cancelledJobList):
        queue = []
        order = 1  # order starts from 1
        for q in acceptedJobList:
            queryjob_id = q["_id"]
            query = {"_id": queryjob_id}
            update = {"$set": {
                "order": order,
                "status": SCHEDULED
            }}
            if not self._collection.find_and_modify(query, update):
                rospy.logerr("Error while writing schedule results!")
                rospy.signal_shutdown("Bye!")

            # Notify updates.
            msg = QueryJobUpdate()
            msg.queryjob_id = str(queryjob_id)
            msg.field_names = ["order", "status"]
            self._pub.publish(msg)

            queue.append(queryjob_id)
            order += 1
        
        for q in cancelledJobList:
            queryjob_id = q["_id"]
            query = {"_id": queryjob_id}
            update = {"$set": {
                "order": order,
                "status": CANCELLED
            }}
            if not self._collection.find_and_modify(query, update):
                rospy.logerr("Error while writing schedule results!")
                rospy.signal_shutdown("Bye!")

            # Notify updates.
            msg = QueryJobUpdate()
            msg.queryjob_id = str(queryjob_id)
            msg.field_names = ["order", "status"]
            self._pub.publish(msg)
            
            queue.append(queryjob_id)
    
    def scheduleJobs(self, rawJobList):
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
        locationsList = []
        newJobList = []
        for job in rawJobList:
            jobIDsList.append(str(job['_id']))
            startTimesList.append(generateDatetimeMsg(job['timeissued']))
            endTimesList.append(generateDatetimeMsg(job['deadline']))
            prioritiesList.append(job['priority'])
            locationsList.append(job['location'])
            newJobList.append(job)
            count += 1
        
        outMsg.numConstraints = count
        outMsg.jobID = jobIDsList
        outMsg.startTimes = startTimesList
        outMsg.endTimes = endTimesList
        outMsg.priority = prioritiesList
        outMsg.location = locationsList
        
        try:
            resp = self.SAT_Scheduler_Service(outMsg)
        except rospy.ServiceException, e:
            print "Service call failed: %s"%e
        
        acceptedJobList = []
        cancelledJobList = []
        for job in newJobList:
            if str(job['_id']) in resp.acceptedJobID:
                acceptedJobList.append(job)
            else:
                cancelledJobList.append(job)
        return acceptedJobList, cancelledJobList
        
    def getAllJobsFromDB(self):
        # Set current running job to scheduled (let be rescheduled)
        self._collection.find_and_modify(
            {"status": RUNNING},
            {"$set": {"status": RECEIVED,
                      "timecompleted": datetime.utcnow().replace(tzinfo=utc)}}
        )
        # Get all recieved, scheduled, and aborted tasks
        query = {"$or": [{"status": RECEIVED}, {"status": SCHEDULED}, {"status": ABORTED}]}
        qr = self._collection.find(query)
        return qr
    
    def confirmResult(self, resp):
        print resp

def generateDatetimeMsg(dt):
    """
    Returns a message from the datetime given.
    """
    dtMsg = datetimemsg()
    dtMsg.year = dt.year
    dtMsg.month = dt.month
    dtMsg.day = dt.day
    dtMsg.hour = dt.hour
    dtMsg.minute = dt.minute
    dtMsg.second = dt.second
    dtMsg.microsecond = dt.microsecond
    return dtMsg
        
if __name__ == '__main__':
    rospack = rospkg.RosPack()
    apiDriver = SATModelerAPISara()
    
