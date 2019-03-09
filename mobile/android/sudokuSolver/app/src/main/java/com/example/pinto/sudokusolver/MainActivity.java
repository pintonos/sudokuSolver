package com.example.pinto.sudokusolver;

import android.content.Intent;
import android.graphics.Bitmap;
import android.net.Uri;
import android.os.Environment;
import android.provider.MediaStore;
import android.support.v4.content.FileProvider;
import android.support.v7.app.AppCompatActivity;
import android.os.Bundle;
import android.util.Log;
import android.view.View;
import android.widget.EditText;
import android.widget.ImageView;
import android.widget.TextView;

import com.android.volley.Request;
import com.android.volley.RequestQueue;
import com.android.volley.Response;
import com.android.volley.VolleyError;
import com.android.volley.toolbox.StringRequest;
import com.android.volley.toolbox.Volley;

import java.io.File;
import java.io.IOException;
import java.text.SimpleDateFormat;
import java.util.Date;

public class MainActivity extends AppCompatActivity {

    public static final String EXTRA_MESSAGE = "com.example.sudokuSolver.MESSAGE";
    public static final String EXTRA_REPONSE = "com.example.sudokuSolver.RESPONSE";

    static final int REQUEST_TAKE_PHOTO = 1;

    private Uri photoURI;


    //tag for logger
    private static final String TAG = "MainActivity";

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        setContentView(R.layout.activity_main);
    }

    public void sendText(View view){
        Intent intent = new Intent(this, DisplayMessageActivity.class);
        EditText editText = (EditText) findViewById(R.id.editText);
        String message = editText.getText().toString();
        intent.putExtra(EXTRA_MESSAGE, message);
        startActivity(intent);

    }

    public void sendRequest(View view){
        final Intent intent = new Intent(this, DisplayRequestResponse.class);

        // Instantiate the RequestQueue.
        RequestQueue queue = Volley.newRequestQueue(this);
        String url ="http://www.google.com";

        System.out.println(url);

        Log.v(TAG, url);

        // Request a string response from the provided URL.
        StringRequest stringRequest = new StringRequest(Request.Method.GET, url,
                new Response.Listener<String>() {
                    @Override
                    public void onResponse(String response) {
                        // Display the first 500 characters of the response string.
                        intent.putExtra(EXTRA_REPONSE,"Response is: "+ response.substring(0,10));
                        Log.v(TAG, response);
                        startActivity(intent);
                    }
                }, new Response.ErrorListener() {
            @Override
            public void onErrorResponse(VolleyError error) {
                intent.putExtra(EXTRA_REPONSE, "That didn't work!");
                startActivity(intent);
                Log.d(TAG, error.getMessage());
            }
        });

        // Add the request to the RequestQueue.
        queue.add(stringRequest);


    }

    public void dispatchTakePictureIntent(View view) {
        Intent takePictureIntent = new Intent(MediaStore.ACTION_IMAGE_CAPTURE);
        // Ensure that there's a camera activity to handle the intent
        if (takePictureIntent.resolveActivity(getPackageManager()) != null) {
            // Create the File where the photo should go
            File photoFile = null;
            try {
                photoFile = createImageFile();
            } catch (IOException ex) {
                // Error occurred while creating the File
            }
            // Continue only if the File was successfully created
            if (photoFile != null) {
                photoURI = FileProvider.getUriForFile(this,
                        "com.example.android.fileprovider",
                        photoFile);
                takePictureIntent.putExtra(MediaStore.EXTRA_OUTPUT, photoURI);
                startActivityForResult(takePictureIntent, REQUEST_TAKE_PHOTO);
            }
        }

    }

    @Override
    protected void onActivityResult(int requestCode, int resultCode, Intent data) {
        ImageView mImageView = findViewById(R.id.imageView);

        if (requestCode == REQUEST_TAKE_PHOTO && resultCode == RESULT_OK) {
            Log.v(TAG, String.valueOf(photoURI));
            Bundle extras = data.getExtras();
            Bitmap imageBitmap = null;
            try {
                imageBitmap = MediaStore.Images.Media.getBitmap(this.getContentResolver(), photoURI);
                mImageView.setImageBitmap(imageBitmap);
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    private File createImageFile() throws IOException {
        // Create an image file name
        String timeStamp = new SimpleDateFormat("yyyyMMdd_HHmmss").format(new Date());
        String imageFileName = "JPEG_" + timeStamp + "_";
        File storageDir = getExternalFilesDir(Environment.DIRECTORY_PICTURES);
        File image = File.createTempFile(
                imageFileName,  /* prefix */
                ".jpg",         /* suffix */
                storageDir      /* directory */
        );

        // Save a file: path for use with ACTION_VIEW intents
        //currentPhotoPath = image.getAbsolutePath();
        Log.v(TAG, image.getAbsolutePath());
        return image;
    }


}
