from functools import reduce
import cv2
import numpy as np
from z3 import *


def all9(vs):
    assert (len(vs) == 9)
    return Distinct(vs)


def solve(A):
    vars = [[Int(str(i) + str(j)) for j in range(9)] for i in range(9)]

    solver = Solver()

    for r in vars:
        for v in r:
            solver.add(1 <= v, v <= 9)

    # predefined values
    for i, row in enumerate(A):
        for j, val in enumerate(row):
            if val > 0:
                solver.add(vars[i][j] == val)

    # condition elements 1 .. 9 in rows and columns
    for j in range(9):
        solver.add(all9(vars[j]))
        solver.add(all9([vars[i][j] for i in range(9)]))

        # determine block
        br = j % 3
        bc = j // 3
        bs = [vars[3 * br + k][3 * bc + l] for k in range(3) for l in range(3)]
        solver.add(all9(bs))

    result = solver.check()  # check for satisfiability
    if result == z3.sat:
        model = solver.model()  # get valuation
        for row in vars:
            print(reduce(lambda s, v: s + str(model[v]) + " ", row, ""))
    else:
        print("no solution found")


# main

# training part

samples = np.loadtxt('trainsamples.data', np.float32)
responses = np.loadtxt('trainresponses.data', np.float32)
responses = responses.reshape((responses.size, 1))

model = cv2.ml.KNearest_create()
model.train(samples, cv2.ml.ROW_SAMPLE, responses)

# testing part

if len(sys.argv) < 2:
    print("usage: python solver.py imageOfSudoku.png")
    exit(-1)

# TODO size to 430x430
im = cv2.imread(sys.argv[1])
out = np.zeros(im.shape, np.uint8)

raster_size = math.ceil((len(out) // 9)) + 2
field_size = len(out)

gray = cv2.cvtColor(im, cv2.COLOR_BGR2GRAY)
blur = cv2.GaussianBlur(gray, (5, 5), 0)
thresh = cv2.adaptiveThreshold(blur, 255, 1, 1, 5, 2)

# finding Contours
_, contours, _ = cv2.findContours(thresh, cv2.RETR_LIST, cv2.CHAIN_APPROX_SIMPLE)

row = []
field = []
_, y_old, _, _ = cv2.boundingRect(contours[0])
for cnt in contours:
        [x, y, w, h] = cv2.boundingRect(cnt)

        area = w * h
        # contour is number of empty field
        if 680 > area > 325 and w > 10 and h > 25:
            roi = thresh[y:y + h, x:x + w]
            roismall = cv2.resize(roi, (10, 10))
            roismall = roismall.reshape((1, 100))
            roismall = np.float32(roismall)
            _, results, _, _ = model.findNearest(roismall, k=1)
            string = str(int((results[0][0])))
            if y + 10 > y_old > y - 10:
                row.append([string, x, y])
            else:
                row.sort(key=lambda x: int(x[1]))
                if len(row) != 0:
                    field.append(row)
                row = [[string, x, y]]
                y_old = y

            # write to output image
            cv2.rectangle(im, (x, y), (x + w, y + h), (0, 255, 0), 2)
            cv2.putText(out, string, (x, y + h), 0, 1, (0, 255, 0))

row.sort(key=lambda x: int(x[1]))
field.append(row)
field = field[::-1]

# compute number of zeros
padded_field = []
for row in field:
    ext_row = [['0', 0, 0]] + row + [['0', field_size, 0]]
    for i in range(0, len(ext_row) - 1):
        distance = ext_row[i + 1][1] - ext_row[i][1]
        if distance > 1.25 * raster_size:
            padded_field.append([distance // raster_size, '0'])
        if i != len(ext_row) - 2:
            padded_field.append([1, ext_row[i + 1][0]])

# create game board
A = [[] for i in range(0, 9)]
i = k = 0
for item in padded_field:
    if i == 9:
        k = k + 1
        i = 0
    for j in range(int(item[0])):
        A[k].append(int(item[1]))
        i = i + 1

# solve sudoku
solve(A)

# cv2.imshow('out', out)
# cv2.waitKey(0)
