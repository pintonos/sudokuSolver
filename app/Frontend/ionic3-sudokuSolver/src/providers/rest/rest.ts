import { HttpClient } from '@angular/common/http';
import { Injectable } from '@angular/core';

/*
  Generated class for the RestProvider provider.

  See https://angular.io/guide/dependency-injection for more info on providers
  and Angular DI.
*/
@Injectable()
export class RestProvider {

  apiUrl = 'https://jsonplaceholder.typicode.com';

  constructor(public http: HttpClient) {
    console.log('Hello RestProvider Provider');
  }

  getUsers(){
    return new Promise(resolve=> {
      this.http.get(this.apiUrl + '/users').subscribe(data => {
        resolve(data);
      }, err => {
        console.log(err);
      });
    });
  }

  addUser(data) {
    return new Promise((resolve, reject) => {
      this.http.post(this.apiUrl+'/users', JSON.stringify(data))
        .subscribe(res => {
          resolve(res);
        }, (err) => {
          reject(err);
        });
    });
  }

  /*transferData(data){
    let headers = new Headers();
    headers.append('Authorization', auth);

    let formData = new FormData();
    formData.append('image', this.imageURL, this.imageName);

    this.http.post("http://192.168.22.4/api-imageUpload", formData, {headers: headers}).subscribe(res => {
      let status = res['status'];
      if(status == 200){
        this.showAlert( "The image was successfully uploaded!");
      }else{
        this.showAlert("upload error");
      }

    }, (err) => {
      var message = "Error in uploading file " + err
      this.showAlert(message);
    });  
  }*/
}
