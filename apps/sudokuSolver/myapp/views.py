from django.views.decorators.csrf import csrf_exempt
from django.http import JsonResponse
from django.views import generic

from django_fine_uploader.fineuploader import SimpleFineUploader
from django_fine_uploader.forms import FineUploaderUploadForm
from django_fine_uploader.views import FineUploaderView

from .models import FineFile

from .src.test import *


class ExampleView(generic.TemplateView):
    template_name = 'myapp/example.html'

class AboutView(generic.TemplateView):
    template_name = 'myapp/about.html'

class SimpleCustomUploaderView(generic.FormView):
    """Example of a not concurrent not chunked upload. A.K.A. Simple upload.
    """
    form_class = FineUploaderUploadForm

    def form_valid(self, form):
        """You could use the ChunkedFineUploader too, it will detect
        it's not a chunked upload, and it will upload anyway.
        from django_fine_uploader.fineuploader import ChunkedFineUploader
        upload = ChunkedFineUploader(form.cleaned_data, concurrent=False)
        ..but if you want a ~ real ~ simple upload:
        """
        upload = SimpleFineUploader(form.cleaned_data)
        upload.save()

        #useless there because wrong view, form, url (uploader)
        result = test(upload.filename, upload.file_path)

        return JsonResponse({'success': True,})

    def form_invalid(self, form):
        data = {'success': False, 'error': '%s' % repr(form.errors)}
        return JsonResponse(data, status=400)


