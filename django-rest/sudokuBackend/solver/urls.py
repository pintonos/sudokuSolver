from django.urls import path

from . import views

urlpatterns = [
    # path('api/sudokuSolver/', views.SudokuListCreate.as_view() ),
    path('api/sudokuSolver/', views.SudokuCreateResponse),
]
