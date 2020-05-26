import PlusPy.pluspy as pluspy
import sys
import os
from importlib import reload


def start(argv):
    os.environ['PLUSPYPATH'] = '.:./PlusPy/modules/lib:./PlusPy/modules/book:./PlusPy/modules/other'
    sys.argv[1:] = argv
    return pluspy.main()
