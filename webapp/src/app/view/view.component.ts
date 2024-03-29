import {Component, OnInit} from '@angular/core';
import {HttpClient} from '@angular/common/http';

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

  errorRequest: any;
  warningRequest: any;

  constructor(private http: HttpClient) {

   }

  ngOnInit() {
    console.log('init view component')
  }

  onFileSelected(event){
    this.selectedFile = <File> event.target.files[0];
    console.log(event);
    console.log(this.selectedFile);
  }

  onUpload(){
    const fd = new FormData();
    fd.append('image', this.selectedFile);
    this.http.post(this.url, fd)
      .subscribe(response => {
        this.response = response
        console.log(this.response);
        this.response = this.response.result.rows
        console.log(this.response);

      }, error => {
        this.errorRequest = "error";
        console.log("error");
      });   
  }

}
