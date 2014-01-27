/*
 * utils.h
 *
 * Created by: C Code Generator
 * Created on: 2014-01-21
 */

#ifndef UTILS_H_
#define UTILS_H_

#include <math.h>

#define PROGRAM_NAME "solver"
#define TRUE 1
#define FALSE 0

/* Hipothesys */
#define Flights	0
#define Reaches	1

/* View prefixes */
#define Reaches_view_1	0
#define Reaches_view_2	1

/* Log of 2 in base 10 */
#define LOG_2 0.69314718
#define BITS(x) ((int) ceil(log((double) x) / (double) LOG_2))

#endif /* UTILS_H_ */
