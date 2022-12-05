#!/usr/bin/python

import os
import sys
import subprocess
import multiprocessing

NR_CPUS = multiprocessing.cpu_count()
MIN_HEAP_SIZE = 1024
MAX_HEAP_SIZE = 4096
STACK_SIZE = 128

input_file =  sys.argv[-1]

cpus = NR_CPUS if "-simulate" not in sys.argv else 1

subprocess.call("java -Xms{}m -Xmx{}m -Xss{}m tlc2.TLC -workers {} {}"
                .format(MIN_HEAP_SIZE, MAX_HEAP_SIZE, STACK_SIZE,
                        cpus, ' '.join(sys.argv[1:])),
                shell=True)
