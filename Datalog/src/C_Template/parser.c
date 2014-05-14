%% fill_Header

#include <string.h>
#include <errno.h>
#include <stdlib.h>
#include <ctype.h>

#include "parser.h"
#include "utils.h"

#define TAM_FACT 50

int create_fact(const char *, Fact *);

int create_fact(const char *temp_fact, Fact *f){
	int i=0;
	char *pos, value[10];

	f->num_values = 0;
	pos = strstr(temp_fact, "(");

	if (pos == NULL || temp_fact[strlen(temp_fact) -1] != ')')
		return FALSE;
	/*
	 * If (pos - temp_atom) > 10 -> Error
	 */

	strncpy(f->id, temp_fact, (pos - temp_fact));
	f->id[(pos - temp_fact)] = '\0';

	/* Jump the separator "(" */
	pos++;
	for (; (*pos) != ')'; pos++){
		if ((*pos) == ','){
			value[i++] = '\0';
			f->values[f->num_values++] = atol(value);
			i = 0;
			continue;
		}

		if (!isdigit(*pos))
			return FALSE;

		value[i++] = (*pos);
	}

	value[i++] = '\0';
	f->values[f->num_values++] = atol(value);

	return TRUE;
}

int parser_get_fact(FILE *fp, int *num_line, Fact *f){
	int c, i=0;
	char line[TAM_FACT];
	while (i < (TAM_FACT - 1)){
		c = fgetc(fp);

		if (feof(fp))
			return -1;

		/* Jump blanks */
		if (c == ' ' || c == '\t')
			continue;

		if (c == '\n'){
			if (num_line) (*num_line)++;
			continue;
		}

		/* End of the sentence */
		if (c == '.'){
			line[i++] = '\0';
			return create_fact(line, f);
		}

		line[i++] = c;
	}

	return FALSE;
}
