ROS-SAT-Schedule-Solver
=======================

Authors
-------

Skyler Peterson - peters8@cs.washington.edu
Alex Sanchez-Stern - alex.sanchezstern@hotmail.com

Overview
--------

This is the SAT encoding plugin for the sara robotics project which is
mostly used on the Dub-E robotics project at UW. Below is an overview
of this ROS package.

- Root
  - This Readme file
  - doc
    - report.tex (latex of report for this project)
  - include (ignore this directory)
  - launch
    - run_sat_scheduler.launch (launch file to run this package in ros)
  - msg (contains message declerations for this ros package)
  - src
    - encoder.py (The actual SAT encoder)
    - SATModeler.py (ROS Node to collect data and call encoder)
    - SATModelerAPIsara.py (ROS Node to collect/interpret tasks in DB)
    - SATModelerAPITest.py (Internal test module, ignore)
  - srv (contains ROS service type declerations for node-to-node comms)
  - test
    - test_sat_queryjob_scheduler.py (Tests for this ROS node and SAT)
    - test_sat_scheduler (Entrypoint for choosing test from rostest)
    - test_sat_scheduler.test (ROS test file (similar to launch file))
    - testutils.py (utility functions for test)
    - visualizer.py (visualizer code to create graphs from schedule res)
  - testFiles (ignore)

Install/Running
---------------

There are two ways in which to run this software. You can either do a
complete installation and run, which allows you to run the encoder in
the entire sara robot system. Unfortunetly this requires both permission
to pull the sara code base and an extensive install process. The other
option is to run the encoder.py file on its own in a command line
environment.

Complete Install
----------------

These instructions expect that you are running Ubuntu 11.04. We have
heard ancient legends that all of the following can be done on other
linux configs, windows, and maybe even MACs. Gob help the soul foolhardy
enough to attempt this though. You will get no help from us.

1) Install ROS (Robotic Operating System) an specifically the Indigo
   distribution. Check this link for instructions.
   
   http://wiki.ros.org/indigo/Installation/Ubuntu
   
2) Get access to the sara repository and pull the 17 repositories as
   described in the project wiki. sara_HRI is the most important.
   
3) Install z3 and setup z3py

4) Install MongoDB and pymongo

   http://www.mongodb.org/
   
5) Install networkx to use the visualizer

   run the following if you do not already have pip
   
   sudo apt-get install python-pip
   
   run the following to install networkx
   
   sudo pip install networkx
   
6) Run the following command once everything is setup to launch this
   project along side sara_HRI
   
   roslaunch sat_schedule_solver run_sat_scheduler.launch
   
7) Run the following to see the test cases run.

   rostest sat_schedule_solver test_sat_scheduler.test


Running the Encoder in Isolation
--------------------------------

These instructions allow you to run the encoder in an isolated
environment.

1) run the encoder.py file in the python shell

  python -i encoder.py
  
2) Now you can create tasks as shown below.

  task = Task(weight, intervals, location, taskID, name)
  
    weight is the priority: 0 is absolute, 1... is relative priorities.
    intervals is a list of time intervals in seconds when the task
              must be completed.
    location is a string location for where the task should take place
    taskID is the name of the task to do at the location.
    name is a string name for this particular job.
    
    example: task = Task(0, [(100, 500), (1000, 2000)], 'CSE014',
                        'securityCheck', 'I_Heard_A_Noise')
                        
      Here an admin task (priority 0) must take place within 100 and 500
      seconds or 1000 to 2000 seconds, at room CSE014, to do a security
      check task.
      
3) Now that you have a list of tasks, create a solver and run it.

   solver = Solver(tasks=[task])
   solver.solveTasks()
   
   This will print a result and also return a path in the graph
   breakdown of the world which can be used to extract the schedule.
