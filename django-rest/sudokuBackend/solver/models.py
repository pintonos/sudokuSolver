import uuid

from django.db import models


def imageFile(instance, filename):
    extension = filename.split(".")[-1]
    return "{}.{}".format(uuid.uuid4(), extension)


class UploadedSudoku(models.Model):
    # name = models.CharField(max_length=100, null=True)
    # email = models.EmailField(null=True)
    # message = models.CharField(max_length=300, null=True)
    created_at = models.DateTimeField(auto_now_add=True)

    image = models.ImageField(
        upload_to=imageFile,
        max_length=254, blank=True, null=True
    )
