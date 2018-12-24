import { Component, OnInit } from '@angular/core';
import { HttpClient } from '@angular/common/http';

@Component({
  selector: 'app-view',
  templateUrl: './view.component.html',
  styleUrls: ['./view.component.css']
})
export class ViewComponent implements OnInit {

  userName: string = "";
  response: any;

  url: string = "http://127.0.0.1:8000/api/sudokuSolver/";
  selectedFile: File = null;

  constructor(private http: HttpClient) {

   }

  ngOnInit() {
    console.log('init view component')
  }

  search(){
    let obs = this.http.get('https://api.github.com/users/' + this.userName);
    obs.subscribe((response) => {
      this.response = response;
      console.log(response);
    })
  }

  onFileSelected(event){
    this.selectedFile = <File> event.target.files[0];
    console.log(event);
  }

  onUpload(){
    /*const fd = new FormData();
    fd.append('image', this.selectedFile, this.selectedFile.name);
    this.http.post(this.url, fd)
      .subscribe(res => {
        console.log(res);
      });*/
      this.http.get('http://127.0.0.1:8000/api/sudokuSolver/')
      .subscribe(res => {
        console.log(res);
      });
  }

}
