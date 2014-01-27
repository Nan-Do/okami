/*
 * parser.h
 *
 * Created by: C Code Generator
 * Created on: 2014-01-21
 */

#ifndef PARSER_H_
#define PARSER_H_

/*
 * This module parses the datalog program
 */

#include <stdio.h>

#include "fact.h"

/*
 * This function handles the facts and fill the Fact structure
 * Returns:
 * 	-1 EOF
 * 	 0 FALSE
 * 	 1 TRUE
 */
extern int parser_get_fact(FILE *, int *, Fact *);

#endif /* PARSER_H_ */
