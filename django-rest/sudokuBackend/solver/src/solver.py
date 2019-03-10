import cv2
import numpy as np
from z3 import *
import math
import os

from backend.settings import BASE_DIR


class Solver:
    SUDOKU_SIZE = 9
    BLOCK_SIZE = 3
    IMAGE_SIZE = 431
    RASTER_SIZE = math.ceil(IMAGE_SIZE // SUDOKU_SIZE) + 2
    BLACK = (0, 0, 0, 0)

    def __init__(self, image):
        self.image = image
        self.model = Solver.train(BASE_DIR + '/solver/resources/data/numbers_samples.data',
                                  BASE_DIR + '/solver/resources/data/numbers_responses.data'
                                  )

    def get_solution(self):
        image = cv2.imread(self.image)

        # prepare image
        image = Solver.prepare_image(image)

        # finding Contours
        contours, _ = cv2.findContours(image, cv2.RETR_LIST, cv2.CHAIN_APPROX_SIMPLE)

        row = []
        field = []
        _, y_old, _, _ = cv2.boundingRect(contours[0])
        for cnt in contours:
            [x, y, w, h] = cv2.boundingRect(cnt)
            area = w * h

            # contour is number of empty field
            if 1500 > area > 170 and w > 10 and h > 14:
                roi = image[y:y + h, x:x + w]
                roi_small = cv2.resize(roi, (10, 10))
                roi_small = roi_small.reshape((1, 100))
                roi_small = np.float32(roi_small)
                _, results, _, _ = self.model.findNearest(roi_small, k=1)
                string = str(int((results[0][0])))
                if y + 10 > y_old > y - 10:
                    row.append([string, x, y])
                else:
                    row.sort(key=lambda z: int(z[1]))
                    if len(row) != 0:
                        field.append(row)
                    row = [[string, x, y]]
                    y_old = y

        row.sort(key=lambda z: int(z[1]))
        field.append(row)
        field = field[::-1]

        # compute number of zeros
        y_old = 0
        padded_field = []
        for row in field:
            ext_row = [['0', 0, 0]] + row + [['0', Solver.IMAGE_SIZE, 0]]
            y_new = row[0][2]
            if y_new - y_old > Solver.RASTER_SIZE * 1.15:
                padded_field.append([9, '0'])
            y_old = y_new
            for i in range(0, len(ext_row) - 1):
                distance = ext_row[i + 1][1] - ext_row[i][1]
                if distance > 1.10 * Solver.RASTER_SIZE:
                    padded_field.append([distance // (Solver.RASTER_SIZE + 1), '0'])
                if i != len(ext_row) - 2:
                    padded_field.append([1, ext_row[i + 1][0]])

        if Solver.IMAGE_SIZE - y_old > Solver.RASTER_SIZE * 1.15:
            padded_field.append([9, '0'])

        # create game board
        mat = Solver.create_board(padded_field)

        # solve sudoku
        return Solver.solve(mat)

    @staticmethod
    def all9(vs):
        assert (len(vs) == Solver.SUDOKU_SIZE)
        return Distinct(vs)

    @staticmethod
    def solve(matrix):
        digits = [[z3.Int(str(i) + str(j)) for j in range(Solver.SUDOKU_SIZE)] for i in range(Solver.SUDOKU_SIZE)]

        z3_solver = z3.Solver()

        for row in digits:
            for dig in row:
                z3_solver.add(1 <= dig, dig <= Solver.SUDOKU_SIZE)

        # predefined values
        for i, row in enumerate(matrix):
            for j, val in enumerate(row):
                if val > 0:
                    z3_solver.add(digits[i][j] == val)

        # condition elements 1 .. 9 in rows and columns
        for j in range(Solver.SUDOKU_SIZE):
            z3_solver.add(Solver.all9(digits[j]))
            z3_solver.add(Solver.all9([digits[i][j] for i in range(9)]))

            # determine block
            br = j % (Solver.SUDOKU_SIZE // Solver.BLOCK_SIZE)
            bc = j // (Solver.SUDOKU_SIZE // Solver.BLOCK_SIZE)
            bs = []
            for k in range((Solver.SUDOKU_SIZE // Solver.BLOCK_SIZE)):
                for l in range((Solver.SUDOKU_SIZE // Solver.BLOCK_SIZE)):
                    bs.append(digits[(Solver.SUDOKU_SIZE // Solver.BLOCK_SIZE) * br + k]
                              [(Solver.SUDOKU_SIZE // Solver.BLOCK_SIZE) * bc + l])
            z3_solver.add(Solver.all9(bs))

        matrix = []
        result = z3_solver.check()  # check for sat
        if result == z3.sat:
            m = z3_solver.model()  # get valuation
            for row in digits:
                result_row = []
                for col in row:
                    result_row.append(m[col].as_long())
                matrix.append(result_row)
        if len(matrix) == 0:
            raise Exception("Sudoku not solvable")
        return matrix

    @staticmethod
    def train(samples, responses):
        samples = np.loadtxt(samples, np.float32)
        responses = np.loadtxt(responses, np.float32)
        responses = responses.reshape((responses.size, 1))
        m = cv2.ml.KNearest_create()
        m.train(samples, cv2.ml.ROW_SAMPLE, responses)
        return m

    @staticmethod
    def align_image(gray):
        contours, _ = cv2.findContours(gray, cv2.RETR_LIST, cv2.CHAIN_APPROX_SIMPLE)

        # get biggest contour, which should be sudoku square
        sorted_contours = sorted(contours, key=lambda c: cv2.contourArea(c), reverse=True)
        biggest = sorted_contours[0]

        # get 4 vertices of sudoku square
        peri = cv2.arcLength(biggest, True)
        src = cv2.approxPolyDP(biggest, 0.02 * peri, True)

        # sort source points according to destination points
        src = sorted(src, key=lambda elem: [elem[0][0] + elem[0][1]])
        src = np.array([elem.tolist() for elem in src])
        if src[1][0][1] < src[2][0][1]:
            src[2][0][0], src[1][0][0] = src[1][0][0], src[2][0][0]
            src[2][0][1], src[1][0][1] = src[1][0][1], src[2][0][1]

        # 4 fixed points in destination image
        destination = np.array([[0, 0],
                                [0, Solver.IMAGE_SIZE],
                                [Solver.IMAGE_SIZE, 0],
                                [Solver.IMAGE_SIZE, Solver.IMAGE_SIZE]]
                               )

        # calculate homography matrix
        h, status = cv2.findHomography(src, destination)
        im_out = cv2.warpPerspective(gray, h, (gray.shape[1], gray.shape[0]))

        return im_out

    @staticmethod
    def prepare_image(image):
        image = cv2.resize(image, (Solver.IMAGE_SIZE, Solver.IMAGE_SIZE))
        gray = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
        blur = cv2.GaussianBlur(gray, (5, 5), 0)
        thresh = cv2.adaptiveThreshold(blur, 255, 1, 1, 5, 2)
        aligned = Solver.align_image(thresh)
        return aligned

    @staticmethod
    def create_board(padded_field):
        matrix = [[] for _ in range(0, Solver.SUDOKU_SIZE)]
        i = k = 0
        for item in padded_field:
            for j in range(int(item[0])):
                if i == Solver.SUDOKU_SIZE:
                    k = k + 1
                    i = 0
                matrix[k].append(int(item[1]))
                i = i + 1
        # assertions
        try:
            assert len(matrix) == Solver.SUDOKU_SIZE
            for row in matrix:
                assert len(row) == Solver.SUDOKU_SIZE
        except AssertionError:
            raise Exception("Not able to recognize all digits in image.")
        return matrix


'''solver = Solver("/home/josef/projects/sudokuSolver/django-rest/sudokuBackend/solver/resources/testdata/23.jpg")
solution = solver.get_solution()
for r in solution:
    print(r)'''