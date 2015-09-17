/*
 ============================================================================
 Name        : hikerdice_branchandbound.c
 Author      : Arthur
 Version     : 0.3
 Copyright   : WTFPL
 Description : Branch and bound algorithm for the Hamiltonian Hiker Dice Problem

 O algoritmo branch and bound é um método exato de busca da melhor solução de um problema,
 baseado na enumeração de todas as possibilidades. Mas, diferentemente de algoritmos força-bruta,
 este evita a busca em caminhos que conhecidamente não levariam à solução do problema.

 A execução do algoritmo segue as seguintes etapas: Inicialmente o vértice origem é adicionado à pilha
 da busca. então, enquanto a pilha não for vazia, visita o elemento no topo da pilha, e adiciona
 todos os seus vértices vizinhos não visitados na pilha, e repete o loop.
 A aplicação do branch and bound esté no momento da inserção dos filhos, verificando se
 a solução parcial ainda pode gerar uma solução válida, através da verificação de:
 -Pontuação máxima possível <= melhor pontuação até agora
 -Bloqueio de vértices vizinhos diferentes do próximo.
 -Desconexão do grafo

 O grafo é armazenado em uma matriz de vértices, onde as arestas existem apenas
 implicitamente, entre cada elemento Vij e seus vizinhos que possuem distï¿½ncia
 euclidiana = 1.
 Os dados (dice) são armazenados em cada um dos vértices, de modo que a
 operação de rolagem não precise alocar memï¿½ria entre cada iteração do loop.
 ============================================================================
 */

#include "hikerdice_branch_and_bound.h"

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <limits.h>
#include <time.h>
#include "dice.h"
#include "graph.h"

/** ================================================= Data =================================*/
vertex** matrix;//uma matriz

int m_, n_;//altura e largura do grafo
int total_free_vertexes;//total de vertices livres (nao pretos)

vertex** stack;//pilha de busca do branch and bound
int head_stack;//cabeca da pilha de busca

vertex* origin;//vertice de saida
vertex** melhor_solucao;//sequencia de vertices da melhor solucao (array de ponteiros)

vertex** solucao_parcial;//sequencia de vertices da melhor solucao (array de ponteiros)
int head_solucao_parcial;//cabeca da solucao parcial

int pontuacao_melhor_solucao;//Pontuacao da melhor solucao
int pontuacao_parcial;//pontuacao parcial sendo construida
int vertex_restantes;

int *pontuacao_max_para_cada_numero_jogadas;

unsigned long long count_branches;
unsigned long long qtd_solucoes_validas;

//parte da busca em profundidade p/ verificar a conexÃ£o do grafo
int vertex_atingidos;
vertex **vertex_visitados_profundidade;

/** ================================================= End Data =================================*/

/*Resolve o mapa usando Branch and bound*/
void solve(){
	add_childs(origin, stack);
	solucao_parcial[-1] = origin;

	while (head_stack >= 0){
		vertex* actual = stack[head_stack];
		if (!actual->visited){
			actual->visited = true;
			vertex_restantes--;
			solucao_parcial[head_solucao_parcial++] = actual;
			roll_dice(actual, solucao_parcial[head_solucao_parcial-2]);
			add_childs(actual, stack);
		}
		else{
			avaliar_melhor_solucao();
			actual->visited = false;
			pontuacao_parcial -= actual->d->bottom;
			head_stack--;
			head_solucao_parcial--;
			vertex_restantes++;
		}
	}
}

/**Conta a quantidade de vizinhos livres de vtx, excluindo o atual*/
int count_vizinhos_livres(vertex *vtx, vertex* atual){
	int i = (*vtx).i;
	int j = (*vtx).j;
	int count = 0;
	if (j>0 && (&matrix[i][j-1] == origin
			|| (!matrix[i][j-1].visited && !matrix[i][j-1].black && &matrix[i][j-1] != atual) ))
		count++;
	if (i>0 && (&matrix[i-1][j] == origin
			|| (!matrix[i-1][j].visited && !matrix[i-1][j].black && &matrix[i-1][j] != atual) ))
		count++;
	if (j<n_-1 && (&matrix[i][j+1] == origin
			|| (!matrix[i][j+1].visited && !matrix[i][j+1].black && &matrix[i][j+1] != atual) ))
		count++;
	if (i<m_-1 && (&matrix[i+1][j] == origin
			|| (!matrix[i+1][j].visited && !matrix[i+1][j].black && &matrix[i+1][j] != atual) ))
		count++;
	return count;
}

/* Verifica se apos a insercao do next, os vizinhos do vertice atual continuam com grau 2,
 * excluindo o vertice vizinho que tambem eh vizinho do destino.
 */
bool vizinhos_atual_tem_grau_2_apos_insercao_next(vertex *atual, vertex *next, vertex *esq, vertex *cima, vertex *dir, vertex *baixo){
	if (atual == origin)
		return true;

	if (esq != NULL && !esq->black && !esq->visited
			&& esq != next && esq != origin && count_vizinhos_livres(esq, atual) < 2)
		return false;
	if (cima != NULL && !cima->black && !cima->visited
			&& cima != next && cima != origin && count_vizinhos_livres(cima, atual) < 2)
		return false;
	if (dir != NULL && !dir->black && !dir->visited
			&& dir != next && dir != origin && count_vizinhos_livres(dir, atual) < 2)
		return false;
	if (baixo != NULL && !baixo->black && !baixo->visited
			&& baixo != next && baixo != origin && count_vizinhos_livres(baixo, atual) < 2)
		return false;
	return true;
}

bool pontuacao_atual_pode_melhorar(){
	int pontuacao_max = pontuacao_max_para_cada_numero_jogadas[vertex_restantes];
	return ((pontuacao_max + pontuacao_parcial) > pontuacao_melhor_solucao);
}



void busca_profundidade(vertex *vtx){
	int i = (*vtx).i;
	int j = (*vtx).j;
	vtx->visited = true;
	vertex_visitados_profundidade[vertex_atingidos++] = vtx;

	vertex * next = NULL;
	if (j > 0) next = &matrix[i][j-1]; else next = NULL;
	if (next != NULL && !next->visited && !next->black){
		busca_profundidade(next);
	}
	if (i>0) next = &matrix[i-1][j]; else next = NULL;
	if (next != NULL && !next->visited && !next->black){
		busca_profundidade(next);
	}
	if (j < n_-1) next = &matrix[i][j+1]; else next = NULL;
	if (next != NULL && !next->visited && !next->black){
		busca_profundidade(next);
	}
	if (i < m_-1) next = &matrix[i+1][j]; else next = NULL;
	if (next != NULL && !next->visited && !next->black){
		busca_profundidade(next);
	}
}

/**
 * Verifica se o grafo está conectado. fazendo uma busca em profundidade, e contando a quantidade de
 * vértices alcançados.
 */
bool grafo_conectado(vertex *next, vertex* atual){
	int vizinhos_livres = count_vizinhos_livres(next, atual);
	if (vizinhos_livres == 1) return true;
	//else if () Verificar o caso em que tem grau 2 ou 3
	vertex_atingidos = 0;

	busca_profundidade(next);

	//Desmarcando os visitados
	for (int i = 0; i < vertex_atingidos; i++){
		vertex_visitados_profundidade[i]->visited = false;
	}

	return (vertex_atingidos == total_free_vertexes - head_solucao_parcial);

}

/* Verifica as condicoees de insercao do next*/
bool insert_conditions(vertex *atual, vertex *next, vertex *esq, vertex *cima, vertex *dir, vertex *baixo){
	if (next == NULL || next->black || next->visited || (next == origin && vertex_restantes > 1))
		return false;
//	if (!pontuacao_atual_pode_melhorar())
//		return false;
	if (!vizinhos_atual_tem_grau_2_apos_insercao_next(atual, next, esq, cima, dir, baixo))
		return false;
//	if (!grafo_conectado(next, atual)){
//		printf("grafo n conectado");
//		return false;
//	}


	return true;
}

/*Adiciona os filhos na seguinte ordem:
 *Esq, Cima, Dir, e baixo
 *Assim, a busca ocorre do sentido anti-horï¿½rio: baixo, dir, cima e esq.
 */
void add_childs(vertex* atual, vertex** stack){
	int i = (*atual).i;
	int j = (*atual).j;
	vertex *vizinhoEsq = NULL;
	vertex *vizinhoCima = NULL;
	vertex *vizinhoDir = NULL;
	vertex *vizinhoBaixo = NULL;
	if (j>0) vizinhoEsq = &matrix[i][j-1];
	if (i>0) vizinhoCima = &matrix[i-1][j];
	if (j<n_-1) vizinhoDir = &matrix[i][j+1];
	if (i<m_-1) vizinhoBaixo = &matrix[i+1][j];

	if (insert_conditions(atual, vizinhoEsq, vizinhoEsq, vizinhoCima, vizinhoDir, vizinhoBaixo)){
		stack[++head_stack] = vizinhoEsq;
		count_branches++;
	}
	if (insert_conditions(atual, vizinhoCima, vizinhoEsq, vizinhoCima, vizinhoDir, vizinhoBaixo)){
		stack[++head_stack] = vizinhoCima;
		count_branches++;
	}
	if (insert_conditions(atual, vizinhoDir, vizinhoEsq, vizinhoCima, vizinhoDir, vizinhoBaixo)){
		stack[++head_stack] = vizinhoDir;
		count_branches++;
	}
	if (insert_conditions(atual, vizinhoBaixo, vizinhoEsq, vizinhoCima, vizinhoDir, vizinhoBaixo)){
		stack[++head_stack] = vizinhoBaixo;
		count_branches++;
	}
}


void avaliar_melhor_solucao(){
	if (head_solucao_parcial == total_free_vertexes && pontuacao_melhor_solucao < pontuacao_parcial){
		for (int i = 0; i < total_free_vertexes; i++){
			melhor_solucao[i] = solucao_parcial[i];
		}
		pontuacao_melhor_solucao = pontuacao_parcial;
		qtd_solucoes_validas++;
		if (pontuacao_parcial == 140)
			printf("pontuacao eh 140");
	}
}


//Rolando o dado para o actualVertex
void roll_dice(vertex* actualVertex, vertex* vertexPai){
	if (vertexPai != NULL){
		dice *dadoAtual = (*actualVertex).d;
		dice *dadoPai = (*vertexPai).d;
		if (relacaoPaiFilho(actualVertex, vertexPai) == 1){
			pontuacao_parcial += roll_left(dadoAtual,dadoPai);//rolando o dado que ja esta no proximo vertice
		}
		else if (relacaoPaiFilho(actualVertex, vertexPai) == 2){
			pontuacao_parcial += roll_up(dadoAtual, dadoPai);//rolando o dado que ja esta no proximo vertice
		}
		else if (relacaoPaiFilho(actualVertex, vertexPai) == 3){
			pontuacao_parcial += roll_right(dadoAtual, dadoPai);//rolando o dado que ja esta no proximo vertice
		}
		else if (relacaoPaiFilho(actualVertex, vertexPai) == 4){
			pontuacao_parcial += roll_down(dadoAtual, dadoPai);//rolando o dado que ja esta no proximo vertice
		}
	}
}

// 1 - esq, 2 - cima, 3 - direita, 4 - baixo
int relacaoPaiFilho(vertex* filho, vertex* pai){
	if((*filho).i == (*pai).i && (*filho).j == (*pai).j-1)
		return 1;
	if((*filho).i == (*pai).i-1 && (*filho).j == (*pai).j)
		return 2;
	if((*filho).i == (*pai).i && (*filho).j == (*pai).j+1)
		return 3;
	if((*filho).i == (*pai).i+1 && (*filho).j == (*pai).j)
		return 4;
	return 0;
}



int main(int argc, char *argv[]) {

	if (argc >= 2){
		FILE *file = fopen( argv[1], "r" );
		if ( file == 0 ){
			printf( "Impossivel abrir arquivo, encerrando\n" );
			return EXIT_SUCCESS;
		}else if (argc >= 4){
			printf("Arquivo encontrado: ");
			printf("%s",argv[1]);
			printf("\n");
			int dice_i_pos = argv[2][0] - 48;
			int dice_j_pos = argv[3][0] - 48;
			init_graph(file, dice_i_pos, dice_j_pos);
		}

		init_data();
		if (total_free_vertexes % 2 != 0){
			printf("O numero de casas livres eh impar. Nao existe solucao para o problema.");
			return EXIT_SUCCESS;
		}
		clock_t t;
		t = clock();
		solve();
		t = clock() - t;
		print_solution(((float)t)/CLOCKS_PER_SEC);
	}
	else {
		printf("Argumentos insuficientes\n" );
	}
	return EXIT_SUCCESS;
}


/**===================================== Funcoes de suporte ==============================================*/
void print_solution(float time_elapsed){
	printf("Solucao encontrada: ");
	if (pontuacao_melhor_solucao > 0){
		int k = 0;
		for (k = 0; k < total_free_vertexes && k < 1000; k++){
			printf("[%d,%d] ", melhor_solucao[k]->i, melhor_solucao[k]->j);
		}
		if (k < total_free_vertexes)
			printf("Solucao muito grande, impressao interrompida.");
	}
	printf("\nValor da melhor pontuacao: %d", pontuacao_melhor_solucao);
	printf("\nNumero de branches: %llu", count_branches);
	if (time_elapsed > 0)
		printf("\nTempo de processamento: %.3f segundos\n", time_elapsed);
	else {
		printf("\nTempo de processamento: 0.000 segundos\n");
	}
	printf("\nQuantidade de solucoes encontradas: %llu\n", qtd_solucoes_validas);
}

void init_data(){
	vertex** solucao_parcial_temp = (vertex**) malloc(sizeof(vertex*)*(total_free_vertexes+1));
	solucao_parcial = &solucao_parcial_temp[1];//Permitindo que o índice -1 guarde o vértice de origem

	head_solucao_parcial = 0;
	pontuacao_parcial = 0;

	melhor_solucao = (vertex**) malloc(sizeof(vertex*)*total_free_vertexes);
	pontuacao_melhor_solucao = 0;

	stack = (vertex**) malloc(sizeof(vertex*)*m_*n_*4);
	head_stack = -1;
	count_branches = 0;
	vertex_restantes = total_free_vertexes;

	//Parte da busca em profundidade
	vertex_visitados_profundidade = (vertex**) malloc(sizeof(vertex*)*total_free_vertexes);
	vertex_atingidos = 0;

	qtd_solucoes_validas = 0;

	config_pontuacao_max();

}

/** Configura o array de pontuacao maxima para N jogadas*/
void config_pontuacao_max(){
	int qtd_jogadas_alocar = total_free_vertexes+1;
	if (qtd_jogadas_alocar < 22)
		qtd_jogadas_alocar = 22;
	pontuacao_max_para_cada_numero_jogadas = malloc((sizeof(int)*qtd_jogadas_alocar));

	pontuacao_max_para_cada_numero_jogadas[0] = 0;
	pontuacao_max_para_cada_numero_jogadas[1] = 6;
	pontuacao_max_para_cada_numero_jogadas[2] = 11;
	pontuacao_max_para_cada_numero_jogadas[3] = 15;
	pontuacao_max_para_cada_numero_jogadas[4] = 21;
	pontuacao_max_para_cada_numero_jogadas[5] = 24;
	pontuacao_max_para_cada_numero_jogadas[6] = 29;
	pontuacao_max_para_cada_numero_jogadas[7] = 33;
	pontuacao_max_para_cada_numero_jogadas[8] = 39;
	pontuacao_max_para_cada_numero_jogadas[9] = 49;
	pontuacao_max_para_cada_numero_jogadas[10] = 47;
	pontuacao_max_para_cada_numero_jogadas[11] = 51;
	pontuacao_max_para_cada_numero_jogadas[12] = 56;
	pontuacao_max_para_cada_numero_jogadas[13] = 59;
	pontuacao_max_para_cada_numero_jogadas[14] = 65;
	pontuacao_max_para_cada_numero_jogadas[15] = 68;
	pontuacao_max_para_cada_numero_jogadas[16] = 74;
	pontuacao_max_para_cada_numero_jogadas[17] = 77;
	pontuacao_max_para_cada_numero_jogadas[18] = 83;
	pontuacao_max_para_cada_numero_jogadas[19] = 86;
	pontuacao_max_para_cada_numero_jogadas[20] = 91;
	pontuacao_max_para_cada_numero_jogadas[21] = 95;
	pontuacao_max_para_cada_numero_jogadas[22] = 100;

	if (total_free_vertexes >= 23){
		for (int vertex_restantes = 23; vertex_restantes <= total_free_vertexes; vertex_restantes++){
			int pontuacao_max = 0;

			if (vertex_restantes%3 == 0)//se é um multiplo exato (trata n == 0)
				pontuacao_max = (vertex_restantes/3 * 6) + (vertex_restantes/3 * 5) + (vertex_restantes/3 * 4);
			else if (vertex_restantes%3 == 1)
				pontuacao_max = (vertex_restantes/3 * 6) + (vertex_restantes/3 * 5) + (vertex_restantes/3 * 4) + 6;
			else if (vertex_restantes%3 == 2)
				pontuacao_max = (vertex_restantes/3 * 6) + (vertex_restantes/3 * 5) + (vertex_restantes/3 * 4) + 6 + 5;

			pontuacao_max_para_cada_numero_jogadas[vertex_restantes] = pontuacao_max;
		}
	}
}


void init_graph(FILE *fp, int dice_i_pos, int dice_j_pos){
	char x;//char lixo

	fscanf (fp, "%d%c", &m_, &x);
	fscanf (fp, "%d%c", &n_, &x);
	int vertex_value = 0;

	matrix = (vertex**) calloc(m_, sizeof(vertex*));
	for (int j = 0; j < m_; j++){
		matrix[j] = (vertex*) calloc(n_, sizeof(vertex));
	}

	for (int i = 0; i < m_; i++){
		for (int j = 0; j < n_; j++){
			fscanf (fp, "%d%c", &vertex_value, &x);
			matrix[i][j].i = i;
			matrix[i][j].j = j;
			matrix[i][j].black = vertex_value == 0;
			matrix[i][j].visited = false;
			matrix[i][j].d = new_dice(i,j);
			if (!matrix[i][j].black)
				total_free_vertexes++;
		}
	}
	fclose(fp);
	origin = &matrix[dice_i_pos][dice_j_pos];
}


