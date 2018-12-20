from django.shortcuts import render

from solverREST.models import UploadedSudoku
from solverREST.serializers import UploadedSudokuSerializer
from rest_framework import generics

from rest_framework.decorators import api_view
from rest_framework.response import Response
from rest_framework import authentication, permissions

from solverREST.solverSRC.Processor import processRequest

from rest_framework import viewsets, filters

# import the logging library
import logging

# Get an instance of a logger
logger = logging.getLogger(__name__)


#see https://www.django-rest-framework.org/api-guide/generic-views/#retrieveupdateapiview for more
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
            return Response({"message": "Got some data!", "result" : a})

    return Response({"message": "Please use post-method"})
