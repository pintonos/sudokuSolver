from django.urls import path

from . import views

urlpatterns = [
    path('', views.index, name='index'),
    path('about/', views.about, name='about'),
    path('solve/', views.solve, name='solve'),
    path('ajax/', views.ajax, name='ajax'),
    path('ajax-upload/', views.import_uploader, name='my_ajax_upload'),
]
