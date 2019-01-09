from rest_framework import serializers

from solver.models import UploadedSudoku


class UploadedSudokuSerializer(serializers.ModelSerializer):
    class Meta:
        model = UploadedSudoku
        # fields = ('id', 'name', 'email', 'message')
        fields = '__all__'
