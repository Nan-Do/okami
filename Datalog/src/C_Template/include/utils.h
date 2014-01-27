%% fill_Header

#ifndef UTILS_H_
#define UTILS_H_

#include <math.h>

%% fill_ProgramName

#define TRUE 1
#define FALSE 0

%% fill_Hypothesis

%% fill_AccessViews

/* Log of 2 in base 10 */
#define LOG_2 0.69314718
#define BITS(x) ((int) ceil(log((double) x) / (double) LOG_2))

#endif /* UTILS_H_ */
