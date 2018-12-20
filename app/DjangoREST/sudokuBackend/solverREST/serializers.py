from rest_framework import serializers
from solverREST.models import UploadedSudoku

class UploadedSudokuSerializer(serializers.ModelSerializer):
    class Meta:
        model = UploadedSudoku
        #fields = ('id', 'name', 'email', 'message')
        fields = '__all__'