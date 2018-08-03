import sys

import cv2
import numpy as np

# training part
samples = np.loadtxt('trainsamples.data', np.float32)
responses = np.loadtxt('trainresponses.data', np.float32)
responses = responses.reshape((responses.size, 1))

model = cv2.ml.KNearest_create()
model.train(samples, cv2.ml.ROW_SAMPLE, responses)

# testing part

if len(sys.argv) < 2:
    print "usage: scan.py imageOfSudoku.png"
    exit(-1)

im = cv2.imread(sys.argv[1])
out = np.zeros(im.shape, np.uint8)
gray = cv2.cvtColor(im, cv2.COLOR_BGR2GRAY)
thresh = cv2.adaptiveThreshold(gray, 255, 1, 1, 11, 2)

_, contours, _ = cv2.findContours(thresh, cv2.RETR_LIST, cv2.CHAIN_APPROX_SIMPLE)

row = []
field = []
for cnt in contours:
    if 1000 > cv2.contourArea(cnt) > 40:
        [x, y, w, h] = cv2.boundingRect(cnt)
        if h > 28:
            cv2.rectangle(im, (x, y), (x + w, y + h), (0, 255, 0), 2)
            roi = thresh[y:y + h, x:x + w]
            roismall = cv2.resize(roi, (10, 10))
            roismall = roismall.reshape((1, 100))
            roismall = np.float32(roismall)
            retval, results, neigh_resp, dists = model.findNearest(roismall, k=1)
            string = str(int((results[0][0])))
            row.append([string, x, y])
            cv2.putText(out, string, (x, y + h), 0, 1, (0, 255, 0))

        if len(row) == 25:
            # sort by x coordinate
            row.sort(key=lambda x: int(x[1]))
            field.append(row)
            row = []

# reverse order
field = field[::-1]

with open(sys.argv[1] + '.txt', "w+") as f:
    for i in range(0, len(field)):
        for j in range(0, len(field[0])):
            f.write(str(field[i][j][0]) + ' ')
        f.write("\n")

cv2.imshow('out', out)
cv2.waitKey(0)
