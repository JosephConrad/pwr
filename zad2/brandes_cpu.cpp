#include <iostream>
#include <stack>
#include "stdio.h"
#include <vector>
#include <math.h>
#include <queue>
#include <cstdio>
#include <set>
#include <fstream>
#include <algorithm>
#include <map>
 
using namespace std;

typedef long long LL;

const int DEBUG = 0;
#define PB push_back  
#define MP make_pair
#define ST first
#define ND second

#define REPF(i,n) for (int i=1; i<=n; i++)
#define REP(i,n) for (int i=0; i<n; i++)
#define FORD(i,a,b) for(int i=(a);i>=(b);--i)
#define FOR(i,a,b) for(int i=(a);i<=(b);++i)

#define FOREACH(i,s) for(VAR(i,(s).begin()); i != (s).end(); i++)
#define VAR(a,b)  __typeof(b) a=(b)
 
//*****************************************************************************
//                            Defined structures
//*****************************************************************************
map<int, vector<int> > graph;
std::vector<int> num_neigh;
int *vmap, *vptrs, *adjs;
const int MAX_NEIGH = 4;

map< int, vector<int> >::iterator it;
int num_virtual = 0;
int num_vertex = 0;

//*****************************************************************************
//                               Function headers
//*****************************************************************************
void print_graph();

// !!! maksymalny numer wierzcholka jest o jeden mniejszy od liczby wierzcholk

void print_vec(std::vector<int> array) 
{
    FOREACH(elt, array)
        cout << *elt << " ";
    cout << endl;
}

void print_array(int* array, int num_virtual)
{
    REP(i, num_virtual) printf("%d ", array[i]);
    printf("\n");
}

int readData(char* fileName) 
{
    int a, b, maxVertex = 0;
    FILE* f = fopen(fileName, "r");
    int num_edges = 0;
    while (fscanf(f, "%d %d", &a, &b) != EOF) {
        num_edges++;
        graph[a].push_back(b);
        graph[b].push_back(a);
        maxVertex = max(maxVertex, max(a, b));
    }
    num_edges *= 2;
    fseek(f, 0, SEEK_SET);
    
    num_vertex = maxVertex + 1;
   
    num_neigh.resize(num_vertex);
    FOREACH(elt, graph)
           num_neigh[elt->first] = elt->second.size();       
    // number of virtual verticies
    REP(i, num_vertex) {
        num_virtual += num_neigh[i]/MAX_NEIGH;
        if (num_neigh[i] % MAX_NEIGH != 0) num_virtual++;
    }

    vmap = (int *) calloc(num_virtual, sizeof(int));
    vptrs = (int *) calloc(num_virtual + 1, sizeof(int));
    adjs = (int *) calloc(num_edges, sizeof(int));
    // wypelnianie tablic  adjs
    int akt_index = 0;
    int e = 0;
    FOREACH(elt, graph) {
        FOREACH(i, elt->second) {
            adjs[e] = *i;
            e++;
        }
    }
      
    int current = 0;
    int ptrs_i = 0;
    int offset = 0;
    
    REP(i, num_vertex) {
        int ile = 0;
        if (num_neigh[i] == 0) continue;
        else {
            ile = (num_neigh[i] -1) /MAX_NEIGH + 1;
        }
        REP(k, ile) {
            vmap[current] = i;
            vptrs[current] = ptrs_i;
            if (k + 1 == ile) ptrs_i += (num_neigh[i]-1) % MAX_NEIGH + 1;
            else
                ptrs_i += MAX_NEIGH;
            current++;
        }
    }
    vptrs[current] = num_edges;
    fclose(f);
    return maxVertex;
}


void print_graph() 
{
	FOREACH(elt,  graph) {
		cout << "Klucz :" << elt->first;
		cout << " Wektor :";
		for (int i = 0; i < elt->second.size(); i++){
			cout << elt->second[i];
			cout << " ";
		}
		cout << endl << endl;
	}
}

int main(int argc, char *argv[]) 
{
	int maks_val = readData(argv[1]);
    float C[num_vertex];
    REP(i, num_vertex) C[i] = 0.0; 
    for (int s = 0; s < num_vertex; s++) {
        int sigma[num_vertex];
		int d[num_vertex];
		float delta[num_vertex];
        REP(i, num_vertex) {
			d[i] = -1;
            sigma[i] = 0;
        }
        sigma[s] = 1;
		d[s] = 0;

        //*********************************************************************
        //                  Forward Phase
        //*********************************************************************
        
        int l = 0;
        int cont = 1;
        while (cont) {
            cont = 0;
            int i;
            for (i = 0; i < num_virtual; i++) // dla kazdego wirtualnego wiercholka
            {
                int u = vmap[i];
                if (d[u] == l) {
                    int j;
                    for (j = vptrs[i]; j < vptrs[i+1]; j++){

                        int v = adjs[j];
                        if (d[v] == -1) {
                            d[v] = l + 1; 
                            cont = 1;
                        }
                        if (d[v] == (l + 1)) sigma[v] = sigma[v] + sigma[u];
                    }
                }
            }
            l++; 
        }
        
        REP(v, num_vertex) 
            delta[v] = (float) (1.0 / sigma[v]);
        
        //*********************************************************************
        //                  Backward  Phase
        //*********************************************************************
        while (l > 1) {
            l = l - 1;
            int i;
            for (i = 0; i < num_virtual; i++) // dla kazdego wirtualnego wierch
            {
                int u = vmap[i];
                if (d[u] == l) {
                    float sum = 0.0;
                    int j;
                    for (j = vptrs[i]; j < vptrs[i+1]; j++){
                        int v = adjs[j];
                        if (d[v] == l+1) sum += delta[v];
                    }                    
                    delta[u] += sum; 
                }
            }
        } 
        REP(v, num_vertex) {
            if (v != s) C[v] = C[v] + (delta[v] * sigma[v] - 1);
        }
	}
	
    REP(i, num_vertex)	{
        printf("%f\n", C[i]);
	}
}
