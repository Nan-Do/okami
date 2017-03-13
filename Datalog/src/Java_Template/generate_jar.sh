#! /bin/sh

# Suppress the output of the rewriting variables to the files
if [ "$1" = "-s" ]; then
	echo "Supressing the emission of the rewriting variables into files"
    sed -in 's:^\([ tab]\+\)write_rewriting_variable:\1//write_rewriting_variable:g' Solver.java
fi

echo "Generating the jar file"
javac StarterMain.java
jar cvfe solver.jar StarterMain *.class