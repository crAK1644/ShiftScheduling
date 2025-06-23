# Shift Scheduling using Google OR-Tools

This C# project implements a **constraint-based shift scheduling system** using [Google OR-Tools](https://developers.google.com/optimization). It models a weekly shift assignment problem for a workforce of 60 employees, aiming to allocate morning, afternoon, and night shifts across various work fields.

##  Features

- Generates a weekly schedule across 7 days and 3 shifts (Morning, Afternoon, Night)
- Distributes employees across three workfields: Cashier, Rayon, and Store
- Includes gender-based distribution logic (e.g., 70% female, 30% male)
- Uses Google OR-Tools for solving constraint satisfaction problems efficiently
- Randomized employee demand per shift to simulate dynamic staffing needs
