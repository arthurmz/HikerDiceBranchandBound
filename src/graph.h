/*
 * graph.h
 *
 *  Created on: 3 de set de 2015
 *      Author: Arthur
 */

#ifndef GRAPH_H_
#define GRAPH_H_

#include <stdbool.h>
#include "dice.h"

/**Atenção para NÃO focar na economia de memória.
 * Se um novo campo aumenta a velocidade de processamento do algoritmo,
 * este deve ser adicionado.
 */
typedef struct v{
	int i, j;
	bool visited;
	bool black;
	dice* d;//dado associado
} vertex;





#endif /* GRAPH_H_ */
