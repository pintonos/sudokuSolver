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

    A = []
    result = solver.check()  # check for satisfiability
    if result == z3.sat:
        model = solver.model()  # get valuation
        for row in vars:
            s = reduce(lambda s, v: s + str(model[v]) + " ", row, "")
            A.append(s)
    return A


def generate_image(A):
    image = np.zeros((210, 210, 4), np.uint8)
    for i, row in enumerate(A, 1):
        cv2.putText(image, row, (25, 22 * i), cv2.FONT_HERSHEY_PLAIN, 1, (255, 255, 255, 255))
    cv2.imshow("Result", image)
    cv2.waitKey(0)


def train(samples, responses):
    samples = np.loadtxt(samples, np.float32)
    responses = np.loadtxt(responses, np.float32)
    responses = responses.reshape((responses.size, 1))
    model = cv2.ml.KNearest_create()
    model.train(samples, cv2.ml.ROW_SAMPLE, responses)
    return model


def get_solution(image):
    image = cv2.imread(image)
    image = cv2.resize(image, (431, 431))
    out = np.zeros(image.shape, np.uint8)

    raster_size = math.ceil((len(out) // 9)) + 2
    field_size = len(out)

    gray = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
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
        for j in range(int(item[0])):
            if i == 9:
                k = k + 1
                i = 0
            A[k].append(int(item[1]))
            i = i + 1

    # solve sudoku
    return solve(A)


# main

model = train('numbers_samples.data', 'numbers_responses.data')
solution = get_solution(sys.argv[1])
for row in solution:
    print(row)
generate_image(solution)
