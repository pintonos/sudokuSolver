from __future__ import unicode_literals

from django.db import models


# Create your models here.

class Document(models.Model):
    document = models.FileField(upload_to='media/documents/')
    uploaded_at = models.DateTimeField(auto_now_add=True)
