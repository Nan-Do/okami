# Crear grafica
echo "set encoding iso_8859_15;
set key left;
set log y; set log x;
set xlabel 'Total number of facts'; set ylabel 'Analisys time';
#set xlabel 'Número total de hechos'; set ylabel 'Tiempo del análisis (sec.)';
#set title 'Analysis time for random inputs over increasing variable domain sizes';
#set terminal postscript 'Helvetica' 18;
set terminal postscript enhanced color 'Helvetica' 18;
set output 'resultado.eps';
plot 'prototype/solutions.dat' u 2:3 w lp title 'Compiler', 'xsb_prolog/solutions.dat' u 2:3 w lp title 'XSB', 'yap_prolog/solutions.dat' u 2:3 w lp title 'YAP'"  | gnuplot
epstopdf resultado.eps
