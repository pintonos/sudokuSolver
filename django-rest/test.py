import cv2
import numpy as np
from z3 import *
import math
y = Int('y')

print(y)

SUDOKU_SIZE = 9

digits = [[Int(str(i) + str(j)) for j in range(SUDOKU_SIZE)] for i in range(SUDOKU_SIZE)]

print(digits)
