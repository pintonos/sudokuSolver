# import the logging library
import logging

from rest_framework import generics
from rest_framework.decorators import api_view
from rest_framework.response import Response

from .Processor import processRequest
from .models import UploadedSudoku
from .serializers import UploadedSudokuSerializer

# Get an instance of a logger
logger = logging.getLogger(__name__)


# see https://www.django-rest-framework.org/api-guide/generic-views/#retrieveupdateapiview for more
class SudokuListCreate(generics.ListCreateAPIView):
    queryset = UploadedSudoku.objects.all()
    serializer_class = UploadedSudokuSerializer


@api_view(['GET', 'POST'])
def SudokuCreateResponse(request):
    if request.method == 'POST':
        file_serializer = UploadedSudokuSerializer(data=request.data)
        if file_serializer.is_valid():
            file_serializer.save()
            a = processRequest(file_serializer.data)
            return Response({"message": "success", "result": a})

    return Response({"message": "use post-method"})
