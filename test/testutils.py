#!/usr/bin/env python

'''Collection of testing utility classes and functions.
'''

# ######################################################################
# Imports
# ######################################################################

# System built-ins
import argparse
import random
import unittest

# SARA
from bson.objectid import ObjectId
from pymongo import MongoClient


# ######################################################################
# Module level constants
# ######################################################################

MAX_EPOCH = 2147483647


# ######################################################################
# Functions
# ######################################################################

def generate_uniq_objectid(collection):
    oid = ObjectId()
    while True:
        if not collection.find_one({"_id": oid}):
            break
        oid = ObjectId()
    return oid


def random_unix_epoch():
    return random.randint(0, MAX_EPOCH)


# ######################################################################
# Classes
# ######################################################################

class TestQueryJobStore(unittest.TestCase):

    def setUp(self):

        parser = argparse.ArgumentParser()
        parser.add_argument("--host", type=str, default="localhost")
        parser.add_argument("--port", type=int, default=27017)
        parser.add_argument(
            "--dbname", type=str, default="test_sara_uw_website")
        parser.add_argument(
            "--collname", type=str, default="test_sara_uw_website")
        args, unknown = parser.parse_known_args()

        self._dbname = args.dbname
        self._collname = args.collname
        self._client = MongoClient(args.host, args.port)
        self._db = self._client[self._dbname]
        self.assertTrue(self._collname not in self._db.collection_names(),
                        "Collection {0} already exists!"
                        "".format(self._collname))
        self._collection = self._db[self._collname]

    def tearDown(self):
        if self._client:
            if self._db:
                if self._collection:
                    print self._db.drop_collection(self._collname)
                print self._client.drop_database(self._dbname)
            print self._client.close()
