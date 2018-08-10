from django.shortcuts import render, redirect
from django.http import HttpResponseRedirect

from .models import Document
from .forms import DocumentForm

from .src.scan import scan


from django.middleware.csrf import get_token
from django.shortcuts import render_to_response
from django.template import RequestContext

from ajaxuploader.views import AjaxFileUploader

# Create your views here.

def index(request):
    documents = Document.objects.all()
    return render(request, 'index.html', { 'documents': documents })

def about(request):
    return render(request, "about.html", {})

def solve(request):
    #scan()
    documents = Document.objects.all()

    if request.method == 'POST':
        form = DocumentForm(request.POST, request.FILES)
        if form.is_valid():
            form.save()
            return redirect('solve')
    else:
        form = DocumentForm()
    return render(request, 'solve.html', {'form': form, 'documents':documents})


def ajax(request):
    csrf_token = get_token(request)
    return render_to_response('import.html',
        {'csrf_token': csrf_token}, context_instance = RequestContext(request))

import_uploader = AjaxFileUploader()
