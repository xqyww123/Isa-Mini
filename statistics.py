#!/bin/env python

USAGE = """
statistics.py <PATH TO THE DATABASE>
"""

from sqlitedict import SqliteDict
import sys
import csv

if len(sys.argv) != 2:
    print(USAGE)
    exit(1)

total = 0
success = 0

with SqliteDict(sys.argv[1]) as db:
    with open('result.csv', 'w', newline='') as f:
        w = csv.writer(f, delimiter=',', quotechar='\"', quoting=csv.QUOTE_MINIMAL)
        for k,v in db.items():
            (file,line) = k.split('#')
            w.writerow([file,line,v[0],v[1]])
            total += 1
            if v[0]:
                success += 1

print(f"{success} / {total}")


