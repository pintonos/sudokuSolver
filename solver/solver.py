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


def read_problem(file_name):
    A = []
    with open(file_name, encoding="utf8", errors='ignore') as f:
        for l in f.readlines():
            row = [int(c) for c in l.strip().split(' ') if c]
            assert (len(row) == 9)
            A.append(row)
    assert (len(A) == 9)
    return A


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
gray = cv2.cvtColor(im, cv2.COLOR_BGR2GRAY)
_, thresh = cv2.threshold(gray, 127, 255, cv2.THRESH_BINARY)
canny = cv2.Canny(im, 127, 255)

_, contours, _ = cv2.findContours(canny, cv2.RETR_LIST, cv2.CHAIN_APPROX_SIMPLE)

row = []
field = []
for cnt in contours:
    if 2200 > cv2.contourArea(cnt) > 500:
        [x, y, w, h] = cv2.boundingRect(cnt)
        if h > 35:
            # k-nearest
            roi = thresh[y:y + h, x:x + w]
            roismall = cv2.resize(roi, (10, 10))
            roismall = roismall.reshape((1, 100))
            roismall = np.float32(roismall)
            _, results, _, _ = model.findNearest(roismall, k=1)
            string = str(int((results[0][0])))
            row.append([string, x, y])
            # print len(row)

            # write to output image
            cv2.rectangle(im, (x, y), (x + w, y + h), (0, 255, 0), 2)
            cv2.putText(out, string, (x, y + h), 0, 1, (0, 255, 0))

        if len(row) == 9:
            # sort by x coordinate
            row.sort(key=lambda x: int(x[1]))
            field.append(row)
            row = []

# reverse order
field = field[::-1]

# cv2.imshow("result", out)
# cv2.waitKey(0)

# write to file
with open(sys.argv[1] + '.txt', "w+") as f:
    for i in range(0, len(field)):
        for j in range(0, len(field[0])):
            f.write(str(field[i][j][0]) + ' ')
        f.write("\n")

# solve sudoku
A = read_problem(sys.argv[1] + '.txt')
solve(A)

# cv2.imshow('out', out)
# cv2.waitKey(0)
