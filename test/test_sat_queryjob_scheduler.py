'''Test execution functionality in query_scheulder node.
'''

# ######################################################################
# Imports
# ######################################################################

# System built-ins
from datetime import datetime as dt
from pytz import utc

# ROS
import rospy
import random

# Local
from sara_queryjob_manager.msg import QueryJobStatus, RunQueryAction
from sara_queryjob_manager.srv import ScheduleQueryJob
from sara_queryjob_manager.simpler_action_server import SimplerActionServer
from testutils import random_unix_epoch


# ######################################################################
# Functions
# ######################################################################

def test_sat_schedule_single_item(self):
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
    timeissued_int = random_unix_epoch()
    timeissued = dt.utcfromtimestamp(timeissued_int).replace(tzinfo=utc)
    deadline_int = timeissued_int + 100
    deadline = dt.utcfromtimestamp(deadline_int).replace(tzinfo=utc)
    priority = 0
    queryjob_id = self._collection.insert({"dummy": None,
                                           "deadline": deadline,
                                           "priority": priority})
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
        if qr[0]["status"] == QueryJobStatus.RUNNING:
            break
        rospy.sleep(0.1)
        loopCount += 1
    
    self.assertEqual(qr[0]["status"], QueryJobStatus.RUNNING)

        
def test_sat_schedule_multiple_items(self):
    '''
    Test the sat scheduler inside the sara_queryjob_scheduler.
    This test will check that many items will be scheduled correctly.
    The test will generate a SAT situation where all jobs are scheduled
    without conflict and the order is easy to determine.
    '''

    # Create a SimpleActionServer.
    rospy.init_node("test_sat_schedule_multiple_items")
    server = SimplerActionServer(
        "/run_query", RunQueryAction)

    # Wait for the service to start.
    rospy.wait_for_service("/schedule_queryjob")
    s = rospy.ServiceProxy("/schedule_queryjob", ScheduleQueryJob)

    # Create test instances.
    N = 50
    test_inputs = []
    for i in range(N):
        timeissued_int = random_unix_epoch()
        timeissued = dt.utcfromtimestamp(timeissued_int).replace(tzinfo=utc)
        queryjob_id = self._collection.insert({"dummy": None})
        test_inputs.append({
            "queryjob_id": queryjob_id,
            "queryjob_id_str": str(queryjob_id),
            "timeissued": timeissued,
            "timeissued_int": timeissued_int
        })
    # Assume QueryJobs are created in order of "timeissued".
    test_inputs.sort(key=lambda x: x["timeissued"])

    # Call service.
    resps = []
    for test_input in test_inputs:
        resp = s(
            test_input["queryjob_id_str"], test_input["timeissued_int"])
        resps.append(resp)
        self.assertTrue(resp.success)

    # Check number of documents in DB.
    self.assertEqual(self._collection.find().count(), N)

    # Start controlling action server.
    r = rospy.Rate(10)
    i = 0
    while True:
        if i == N:
            break
        if not server._as.is_active():
            r.sleep()
            continue

        test_input = test_inputs[i]

        # DB state check after the goal is accepted.
        qr = self._collection.find({
            "_id": test_input["queryjob_id"],
            "order": {"$exists": True}  # could be renewed to 1
        })
        self.assertEqual(qr.count(), 1)
        self.assertEqual(
            qr[0]["timeissued"].replace(tzinfo=utc), test_input["timeissued"])
        self.assertEqual(qr[0]["status"], QueryJobStatus.RUNNING)

        a = random.choice(["s", "p", "a"])
        if a == "s":
            server.succeed()
        elif a == "p":
            server.preempt()
        elif a == "a":
            server.abort()
        r.sleep()  # wait until client updates DB
        # should get notified by topic in future.

        # DB state check when done action.
        qr = self._collection.find({
            "_id": test_input["queryjob_id"],
            "order": {"$exists": True}  # could be renewed to 1
        })
        self.assertEqual(qr.count(), 1)
        self.assertEqual(
            qr[0]["timeissued"].replace(tzinfo=utc), test_input["timeissued"])
        if a == "s":
            self.assertEqual(qr[0]["status"], QueryJobStatus.SUCCEEDED)
        elif a == "p":
            self.assertEqual(qr[0]["status"], QueryJobStatus.CANCELLED)
        elif a == "a":
            self.assertEqual(qr[0]["status"], QueryJobStatus.FAILED)

        i += 1
