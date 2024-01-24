#!/bin/bash

PKG="../rtl/pkg/*.sv"
RTL="../rtl/*.sv"
TB="./*.sv"

xrun -timescale 1ns/1ps \
    $PKG $RTL $TB \
    -gui -access +rwc \
    -input simvision.tcl