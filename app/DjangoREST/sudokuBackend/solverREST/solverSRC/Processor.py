import logging
from rest_framework.renderers import JSONRenderer
from solverREST.solverSRC.Solver import get_solution
import cv2
import os

import json

from django.http import HttpResponse

from sudokuBackend.settings import MEDIA_ROOT, BASE_DIR

# Get an instance of a logger
logger = logging.getLogger(__name__)


def processRequest(data):
    imagePath = data['image']
    imageName = imagePath.split('/')[2]
    logger.error(imageName)
    solution = get_solution(os.path.join(MEDIA_ROOT, imageName))
    logger.error(solution)

    response_data = {}
    response_data['rows'] = solution

    return response_data