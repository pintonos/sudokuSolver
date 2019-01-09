import logging
import os

from backend.settings import MEDIA_ROOT
from .src.solver import get_solution

# Get an instance of a logger
logger = logging.getLogger(__name__)


def processRequest(data):
    image_path = data['image']
    image_name = image_path.split('/')[2]
    logger.error(image_name)
    solution = get_solution(os.path.join(MEDIA_ROOT, image_name))
    logger.error(solution)

    response_data = {'rows': solution}

    return response_data
