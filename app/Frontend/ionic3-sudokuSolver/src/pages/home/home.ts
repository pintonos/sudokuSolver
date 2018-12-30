import { Component } from '@angular/core';
import { NavController } from 'ionic-angular';
import { RestProvider } from '../../providers/rest/rest'

import { Camera, CameraOptions } from '@ionic-native/camera';

const options: CameraOptions = {
  quality: 100,
  destinationType: this.camera.DestinationType.FILE_URI,
  encodingType: this.camera.EncodingType.JPEG,
  mediaType: this.camera.MediaType.PICTURE
}

@Component({
  selector: 'page-home',
  templateUrl: 'home.html'
})
export class HomePage {

  users: any;
  public base64Image: string;

  constructor(public navCtrl: NavController, public restProvider: RestProvider, public camera: Camera) {
    this.getUsers();
  }

  goAdduserPage() {
    this.navCtrl.push('AdduserPage', {});
  }

  getUsers() {
    this.restProvider.getUsers()
    .then(data => {
      this.users = data;
      console.log(this.users);
    });
  }

  takeImage(){
    this.camera.getPicture(options).then((imageData) => {
      // imageData is either a base64 encoded string or a file URI
      // If it's base64 (DATA_URL):
      let base64Image = 'data:image/jpeg;base64,' + imageData;
     }, (err) => {
      // Handle error
     });
    }


}
