from django.shortcuts import render, redirect
from django.http import HttpResponseRedirect

from .models import Document
from .forms import DocumentForm

# Create your views here.

def index(request):
    documents = Document.objects.all()
    return render(request, 'index.html', { 'documents': documents })

def about(request):
    return render(request, "about.html", {})

def upload(request):
    if request.method == 'POST':
        form = DocumentForm(request.POST, request.FILES)
        if form.is_valid():
            form.save()
            return redirect('index')
    else:
        form = DocumentForm()
    return render(request, 'upload.html', {'form': form})
