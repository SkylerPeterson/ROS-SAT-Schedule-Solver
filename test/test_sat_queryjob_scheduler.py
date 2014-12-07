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
from testutils import TestWorldmap


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
    priority = [0]
    location = ['Room01']
    taskId = ['Task01']
    world = TestWorldmap(location, taskId)
    queryjob_id = self._collection.insert({"dummy": None,
                                           "deadline": deadline,
                                           "priority": priority[0],
                                           "location": location[0],
                                           "taskId": taskId[0]})
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
        self.assertEqual(qr[0]["priority"], priority[0])
        self.assertEqual(qr[0]["location"], location[0])
        if qr[0]["status"] == QueryJobStatus.RUNNING:
            break
        rospy.sleep(0.1)
        server.succeed()
        loopCount += 1
    
    self.assertEqual(qr[0]["status"], QueryJobStatus.RUNNING)
    
    createGraphVisualization(world, self._collection.find()) # DEBUG
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
    priority = [0]
    locations = ['Room01', 'Room02', 'Room03', 'Room04']
    taskIds = ['Task01']
    world = TestWorldmap(locations, taskIds)
    queryjob_id = self._collection.insert({"dummy": None,
                                           "deadline": deadline,
                                           "priority": priority[0],
                                           "location": locations[2],
                                           "taskId": taskIds[0]})
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
        self.assertEqual(qr[0]["priority"], priority[0])
        self.assertEqual(qr[0]["location"], locations[2])
        if qr[0]["status"] == QueryJobStatus.RUNNING:
            break
        rospy.sleep(0.1)
        server.succeed()
        loopCount += 1
    
    self.assertEqual(qr[0]["status"], QueryJobStatus.RUNNING)
    
    createGraphVisualization(world, self._collection.find()) # DEBUG
    # Shutdown the worldmap test service class so not to intefere with other tests.
    world.shutdown()


def test_sat_schedule_multiple_tasks_multiple_locations(self):
    '''
    Test the sat scheduler inside the sara_queryjob_scheduler.
    This test will check that many items will be scheduled correctly.
    The test will generate a SAT situation where all jobs are scheduled
    without conflict and the order is easy to determine.
    '''
    # Create a SimpleActionServer.
    rospy.init_node("test_sat_schedule_single_item")
    server = SimplerActionServer(
        "/run_query", RunQueryAction)

    # Wait for the service to start.
    rospy.wait_for_service("/schedule_queryjob")
    s = rospy.ServiceProxy("/schedule_queryjob", ScheduleQueryJob)

    # Create test instances.
    N = 10
    taskNum = 3
    priority = [0 for x in range(0, N)]
    locations = ['Room' + str(x) for x in range(1, N+1)]
    taskIds = ['Task' + str(x) for x in range(1, taskNum+1)]
    taskTimes = [random.choice(range(50, 1001, 10)) for x in range(0, taskNum)]
    world = TestWorldmap(locations, taskIds, taskTimes)
    
    timeissued_int = []
    timeissued = []
    deadline_int = []
    deadline = []
    locationsSorted = []
    queryjob_ids = []
    queryjob_id_strs = []
    baseline = int(time.time())
    for i in range(0, N):
        timeissued_int.append(random_unix_epoch(baseline, baseline + 10000))
        timeissued.append(dt.utcfromtimestamp(timeissued_int[i]).replace(tzinfo=utc))
        deadline_int.append(random_unix_epoch(timeissued_int[i] + 10000, timeissued_int[i] + 20000))
        deadline.append(dt.utcfromtimestamp(deadline_int[i]).replace(tzinfo=utc))
        location = random.choice(locations)
        locationsSorted.append(location)
        locations.remove(location)
        taskId = random.choice(taskIds)
        queryjob_ids.append(self._collection.insert({"dummy": None,
                                                     "deadline": deadline[i],
                                                     "priority": priority[i],
                                                     "location": location,
                                                     "taskId": taskId}))
        queryjob_id_strs.append(str(queryjob_ids[i]))
        baseline = deadline_int[i] + 1000 + taskTimes[taskIds.index(taskId)] + 10000

        # Call service.
        resp = s(queryjob_id_strs[i], timeissued_int[i])
        self.assertTrue(resp.success)
    
    # Check number of documents in DB.
    self.assertEqual(self._collection.find().count(), N)

    loopCount = 0
    i = 0
    while (i < N):
        if not server._as.is_active():
            time.sleep(0.1)
            continue
        queryjob_id = queryjob_ids[i]
        
        # DB state check after the goal is accepted.
        qr = self._collection.find({
            "_id": queryjob_id,
            "order": {"$exists": True}
        })
        self.assertEqual(qr.count(), 1)
        self.assertEqual(qr[0]["timeissued"].replace(tzinfo=utc), timeissued[i])
        self.assertEqual(qr[0]["deadline"].replace(tzinfo=utc), deadline[i])
        self.assertEqual(qr[0]["priority"], priority[i])
        self.assertEqual(qr[0]["location"], locationsSorted[i])
        server.succeed() # We need to succeed for the previous wait
        for maxIter in range(0, 100):
            if qr[0]["status"] == QueryJobStatus.RUNNING:
                break
            time.sleep(1)
        self.assertEqual(qr[0]["status"], QueryJobStatus.RUNNING, "Job not running: " + str(qr[0]))
    
        server.succeed()
        
        # DB state check when done action.
        qr = self._collection.find({
            "_id": queryjob_id,
            "order": {"$exists": True}
        })
        self.assertEqual(qr.count(), 1)
        self.assertEqual(qr[0]["timeissued"].replace(tzinfo=utc), timeissued[i])
        self.assertEqual(qr[0]["deadline"].replace(tzinfo=utc), deadline[i])
        self.assertEqual(qr[0]["priority"], priority[i])
        self.assertEqual(qr[0]["location"], locationsSorted[i])
        for maxIter in range(0, 100):
            if qr[0]["status"] == QueryJobStatus.SUCCEEDED:
                break
            time.sleep(1)
        self.assertEqual(qr[0]["status"], QueryJobStatus.SUCCEEDED, "Job not succeeding: " + str(qr[0]))
        i += 1
    
    createGraphVisualization(world, self._collection.find()) # DEBUG
    # Shutdown the worldmap test service class so not to intefere with other tests.
    world.shutdown()
