# tutorial from
# https://stackoverflow.com/questions/9413216/simple-digit-recognition-ocr-in-opencv-python

import sys

import numpy as np
import cv2

# images should be sized roughly to 400x400

if len(sys.argv) < 2:
    print "usage: python generateTrainData.py {trainImage1, trainImage2, ...}"
    exit(-1)

responses = []
samples = np.empty((0, 100))

for i in range(1, len(sys.argv)):
    im = cv2.imread(sys.argv[i])
    im3 = im.copy()

    gray = cv2.cvtColor(im, cv2.COLOR_BGR2GRAY)
    blur = cv2.GaussianBlur(gray, (5, 5), 0)
    thresh = cv2.adaptiveThreshold(blur, 255, 1, 1, 5, 2)

    # finding Contours

    _, contours, _ = cv2.findContours(thresh, cv2.RETR_LIST, cv2.CHAIN_APPROX_SIMPLE)

    keys = [i for i in range(48, 58)]

    for cnt in contours:
        if 2500 > cv2.contourArea(cnt) > 130:
            [x, y, w, h] = cv2.boundingRect(cnt)
            if h > 30:
                cv2.rectangle(im, (x, y), (x + w, y + h), (0, 0, 255), 2)
                roi = thresh[y:y + h, x:x + w]
                roismall = cv2.resize(roi, (10, 10))
                cv2.imshow('norm', im)
                key = cv2.waitKey(0)

                cv2.rectangle(im, (x, y), (x + w, y + h), (0, 255, 0), 2)

                if key == 27:  # (escape to quit)
                    sys.exit()
                elif key in keys:
                    responses.append(int(chr(key)))
                    sample = roismall.reshape((1, 100))
                    samples = np.append(samples, sample, 0)

responses = np.array(responses, np.float32)
responses = responses.reshape((responses.size, 1))


print "training complete"

np.savetxt('trainsamples.data', samples)
np.savetxt('trainresponses.data', responses)
