'''Test execution functionality in query_scheulder node.
'''

# ######################################################################
# Imports
# ######################################################################

# System built-ins
from datetime import datetime as dt
from pytz import utc
import time

# ROS
import rospy
import random

# Local
from sara_queryjob_manager.msg import QueryJobStatus, RunQueryAction
from sara_queryjob_manager.srv import ScheduleQueryJob
from sara_queryjob_manager.simpler_action_server import SimplerActionServer
from visualizer import createGraphVisualization
from testutils import random_unix_epoch
from testutils import TestSingleTaskWorldmap


# ######################################################################
# Functions
# ######################################################################

def test_sat_schedule_single_task_single_location(self):
    '''
    Test the sat scheduler inside the sara_queryjob_scheduler.
    This test will check that a single item will be scheduled,
    it cannot be an UNSAT situation and should be easy.
    '''
    # Create a SimpleActionServer.
    rospy.init_node("test_sat_schedule_single_item")
    server = SimplerActionServer(
        "/run_query", RunQueryAction)

    # Wait for the service to start.
    rospy.wait_for_service("/schedule_queryjob")
    s = rospy.ServiceProxy("/schedule_queryjob", ScheduleQueryJob)

    # Create test instances.
    timeissued_int = random_unix_epoch(int(time.time()) + 101)
    timeissued = dt.utcfromtimestamp(timeissued_int).replace(tzinfo=utc)
    deadline_int = timeissued_int + 100
    deadline = dt.utcfromtimestamp(deadline_int).replace(tzinfo=utc)
    priority = 0
    location = 'Room01'
    taskId = 'Task01'
    world = TestSingleTaskWorldmap(location, taskId)
    queryjob_id = self._collection.insert({"dummy": None,
                                           "deadline": deadline,
                                           "priority": priority,
                                           "location": location,
                                           "taskId": taskId})
    queryjob_id_str = str(queryjob_id)

    # Call service.
    resp = s(queryjob_id_str, timeissued_int)
    self.assertTrue(resp.success)

    # Check number of documents in DB.
    self.assertEqual(self._collection.find().count(), 1)

    loopCount = 0
    while (loopCount < 100):
        # DB state check after the goal is accepted.
        qr = self._collection.find({
            "_id": queryjob_id,
            "order": {"$exists": True}  # could be renewed to 1
        })
        self.assertEqual(qr.count(), 1)
        self.assertEqual(qr[0]["timeissued"].replace(tzinfo=utc), timeissued)
        self.assertEqual(qr[0]["deadline"].replace(tzinfo=utc), deadline)
        self.assertEqual(qr[0]["priority"], priority)
        self.assertEqual(qr[0]["location"], location)
        if qr[0]["status"] == QueryJobStatus.RUNNING:
            break
        rospy.sleep(0.1)
        loopCount += 1
    
    self.assertEqual(qr[0]["status"], QueryJobStatus.RUNNING)
    
    createGraphVisualization(world, self._collection.find())
    # Shutdown the worldmap test service class so not to intefere with other tests.
    world.shutdown()

        
def test_sat_schedule_single_task_multiple_locations(self):
    '''
    Test the sat scheduler inside the sara_queryjob_scheduler.
    This test will check that a single task is scheduled among
    many locations.
    '''
    # Create a SimpleActionServer.
    rospy.init_node("test_sat_schedule_single_item")
    server = SimplerActionServer(
        "/run_query", RunQueryAction)

    # Wait for the service to start.
    rospy.wait_for_service("/schedule_queryjob")
    s = rospy.ServiceProxy("/schedule_queryjob", ScheduleQueryJob)

    # Create test instances.
    timeissued_int = random_unix_epoch(int(time.time()) + 101)
    timeissued = dt.utcfromtimestamp(timeissued_int).replace(tzinfo=utc)
    deadline_int = timeissued_int + 100
    deadline = dt.utcfromtimestamp(deadline_int).replace(tzinfo=utc)
    priority = 0
    location = 'Room01'
    taskId = 'Task01'
    world = TestSingleTaskWorldmap(location, taskId)
    queryjob_id = self._collection.insert({"dummy": None,
                                           "deadline": deadline,
                                           "priority": priority,
                                           "location": location,
                                           "taskId": taskId})
    queryjob_id_str = str(queryjob_id)

    # Call service.
    resp = s(queryjob_id_str, timeissued_int)
    self.assertTrue(resp.success)

    # Check number of documents in DB.
    self.assertEqual(self._collection.find().count(), 1)

    loopCount = 0
    while (loopCount < 100):
        # DB state check after the goal is accepted.
        qr = self._collection.find({
            "_id": queryjob_id,
            "order": {"$exists": True}  # could be renewed to 1
        })
        self.assertEqual(qr.count(), 1)
        self.assertEqual(qr[0]["timeissued"].replace(tzinfo=utc), timeissued)
        self.assertEqual(qr[0]["deadline"].replace(tzinfo=utc), deadline)
        self.assertEqual(qr[0]["priority"], priority)
        self.assertEqual(qr[0]["location"], location)
        if qr[0]["status"] == QueryJobStatus.RUNNING:
            break
        rospy.sleep(0.1)
        loopCount += 1
    
    self.assertEqual(qr[0]["status"], QueryJobStatus.RUNNING)
    
    createGraphVisualization(world, self._collection.find())
    # Shutdown the worldmap test service class so not to intefere with other tests.
    world.shutdown()


def test_sat_schedule_multiple_tasks_multiple_locations(self):
    '''
    Test the sat scheduler inside the sara_queryjob_scheduler.
    This test will check that many items will be scheduled correctly.
    The test will generate a SAT situation where all jobs are scheduled
    without conflict and the order is easy to determine.
    '''
    pass
