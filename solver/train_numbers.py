from os import walk
import numpy as np
import cv2

BASE_DIR = './traindata/numbers/'


def train(target, image_file, responses, samples):
    im = cv2.imread(BASE_DIR + target + image_file)
    for i in range(36, 39):
        im = cv2.resize(im, (i, i))
        gray = cv2.cvtColor(im, cv2.COLOR_BGR2GRAY)
        blur = cv2.GaussianBlur(gray, (5, 5), 0)
        thresh = cv2.adaptiveThreshold(blur, 255, 1, 1, 5, 2)

        _, contours, _ = cv2.findContours(thresh, cv2.RETR_LIST, cv2.CHAIN_APPROX_SIMPLE)
        [x, y, w, h] = cv2.boundingRect(contours[-1])  # get last (biggest) contour
        cv2.rectangle(im, (x, y), (x + w, y + h), (0, 0, 255), 2)
        roi = thresh[y:y + h, x:x + w]
        roi_small = cv2.resize(roi, (10, 10))

        responses.append(int(target))
        sample = roi_small.reshape((1, 100))
        samples = np.append(samples, sample, 0)
    return responses, samples


# main

folder = []
for (dirpath, dirnames, filenames) in walk(BASE_DIR):
    folder.extend(dirnames)
    break

responses = []
samples = np.empty((0, 100))
image_paths = []

for subfolder in folder:
    for (dirpath, dirnames, filenames) in walk(BASE_DIR + subfolder):
        for file in filenames:
            responses, samples = train(subfolder, '/' + file, responses, samples)
        break

# save data

responses = np.array(responses, np.float32)
responses = responses.reshape((responses.size, 1))
np.savetxt('numbers_samples.data', samples)
np.savetxt('numbers_responses.data', responses)
