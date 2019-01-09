package com.example.pinto.sudokusolver;

import android.content.Intent;
import android.support.v7.app.AppCompatActivity;
import android.os.Bundle;
import android.widget.ArrayAdapter;
import android.widget.GridView;
import android.widget.TextView;

import java.util.ArrayList;

public class DisplayRequestResponse extends AppCompatActivity {

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        setContentView(R.layout.activity_display_request_response);

        // Get the Intent that started this activity and extract the string
        Intent intent = getIntent();
        String message = intent.getStringExtra(MainActivity.EXTRA_REPONSE);

        // Capture the layout's TextView and set the string as its text
        TextView textView = findViewById(R.id.textViewResponse);
        textView.setText(message);

        GridView gridview = (GridView) findViewById(R.id.gridview1);

        ArrayList<Integer> test = new ArrayList<>();
        for(int j = 0; j < 81; j++){
            test.add(j+1);
        }

        ArrayAdapter<Integer> adapter = new ArrayAdapter<Integer>(this,
                R.layout.grid_item, test);
        gridview.setAdapter(adapter);

        /*gridview = (GridView) findViewById(R.id.gridview2);
        gridview.setAdapter(adapter);*/



    }
}
