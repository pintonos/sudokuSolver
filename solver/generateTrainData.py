import sys
import os.path

import numpy as np
import cv2

if len(sys.argv) < 2:
    print("usage: python generateTrainData.py ./path/to/traindata.txt")
    exit(-1)

# read in training data image paths
training_files = []
with open(sys.argv[1]) as f:
    for line in f.readlines():
        training_files.append(line)

# remove whitespaces
training_files = [x.strip() for x in training_files]

responses = []
samples = np.empty((0, 100))

for train_file in training_files:
    # TODO size to 430x430

    im = cv2.imread(train_file)

    gray = cv2.cvtColor(im, cv2.COLOR_BGR2GRAY)
    _, thresh = cv2.threshold(gray, 127, 255, cv2.THRESH_BINARY)

    canny = cv2.Canny(im, 127, 255)

    # finding Contours

    _, contours, _ = cv2.findContours(canny, cv2.RETR_LIST, cv2.CHAIN_APPROX_SIMPLE)

    keys = [i for i in range(48, 58)]

    cv2.destroyAllWindows()
    for cnt in contours:
        if 2400 > cv2.contourArea(cnt) > 150:
            print(cv2.contourArea(cnt))
            [x, y, w, h] = cv2.boundingRect(cnt)
            if h > 30:
                cv2.rectangle(im, (x, y), (x + w, y + h), (0, 0, 255), 2)
                roi = thresh[y:y + h, x:x + w]
                roismall = cv2.resize(roi, (10, 10))
                cv2.imshow(train_file, im)
                key = cv2.waitKey(0)

                cv2.rectangle(im, (x, y), (x + w, y + h), (0, 255, 0), 2)

                if key == 27:  # escape to quit
                    break
                if key == 32:
                    continue  # space to skip contour
                elif key in keys:
                    responses.append(int(chr(key)))
                    sample = roismall.reshape((1, 100))
                    samples = np.append(samples, sample, 0)

responses = np.array(responses, np.float32)
responses = responses.reshape((responses.size, 1))

print("training complete")

np.savetxt('trainsamples.data', samples)
np.savetxt('trainresponses.data', responses)
