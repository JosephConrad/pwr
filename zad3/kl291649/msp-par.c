//Konrad Lisiecki 291649
#include <stdio.h>
#include <stdlib.h>
#include <mpi.h>
#include <math.h>
#include "matgen.h"
 
#define LLI long long int
#define PB push_back  
#define MP make_pair
#define ST first
#define ND second

#define REPF(i,n) for (int i=1; i<=n; i++)
#define REP(i,n) for (int i=0; i<n; i++)
#define FORD(i,a,b) for(int i=(a);i>=(b);--i)
#define FOR(i,a,b) for(int i=(a);i<=(b);++i)
 
#define VAR(a,b)  __typeof(b) a=(b)
 
static void printUsage(char const * prog)
{
    fprintf(stderr, "Usage:\n");
    fprintf(stderr, "    %s <num_rows> <num_colums> <seed>\n\n", prog);
}

static void printMatrix(LLI const * m, int r, int c)
{
    int i, j;
    for (i = 0; i <= r; ++i)
    {
        for (j = 0; j <= c; ++j)
        {
            printf(" %lld", *m++);
        }
        printf("\n");
    }
    printf("\n");
}
 
int main(int argc, char * argv[])
{

    //--------------------------------------------------------------------------
    //                  Variables
    //--------------------------------------------------------------------------
    int numProcesses, myRank;
    int rows_no, columns_no, seed, N, M;
    LLI *a, *sum, cand, buffer[5], *recvbuf;
    matgen_t * matgenPtr;
    char *name;

    MPI_Init(&argc, &argv);

    //--------------------------------------------------------------------------
    //              Process data and matrix cration 
    //--------------------------------------------------------------------------

    if (argc != 4)
    {
        fprintf(stderr, "ERROR: Invalid arguments!\n");
        printUsage(argv[0]);
        MPI_Finalize();
        exit(1);
    }

    rows_no = atoi(argv[1]);
    columns_no = atoi(argv[2]);
    seed = atoi(argv[3]);

    M = rows_no;
    N = columns_no;

    if (rows_no <= 0 || columns_no <= 0 || seed <= 0)
    {
        fprintf(stderr, "ERROR: Invalid arguments: %s %s %s!\n", argv[1],
                argv[2], argv[3]);
        printUsage(argv[0]);
        MPI_Finalize();
        exit(1);
    }
    matgenPtr = matgenNew(rows_no, columns_no, seed);

    if (matgenPtr == NULL)
    {
        fprintf(stderr, "ERROR: Unable to create the matrix generator!\n");
        printUsage(argv[0]);
        MPI_Finalize();
        exit(1);
    }
    a = (LLI *) malloc(
            sizeof(LLI) * (rows_no + 1) * (columns_no + 1));
    if (a == NULL)
    {
        fprintf(stderr, "ERROR: Unable to create the matrix!\n");
        printUsage(argv[0]);
        MPI_Finalize();
        exit(1);
    }

    sum = (LLI *) calloc((rows_no + 1) * (columns_no + 1), sizeof(LLI));
    if (sum == NULL)
    {
        fprintf(stderr, "ERROR: Unable to create the matrix!\n");
        printUsage(argv[0]);
        MPI_Finalize();
        exit(1);
    }
    for (int j = 1; j <= rows_no; ++j)
    {
        for (int i = 1; i <= columns_no; ++i)
        {
            a[j * (columns_no + 1) + i] = matgenGenerate(matgenPtr);
        }
    }
    matgenDestroy(matgenPtr);

    double startTime;
    double endTime;
    double executionTime; 

    //------------------------------------------------------------------------------
    //                  Start of Computation
    //------------------------------------------------------------------------------
    MPI_Comm_size(MPI_COMM_WORLD, &numProcesses);
    MPI_Comm_rank(MPI_COMM_WORLD, &myRank);

    //------------------------------------------------------------------------------
    //                  Time started - parallelized computation of 2D MSP
    //------------------------------------------------------------------------------
    startTime = MPI_Wtime();

    //------------------------------------------------------------------------------
    //                  Prefix sum calculation
    //------------------------------------------------------------------------------
    int off = N + 1;
    FOR(k, 1, M) {
        FOR(l, 1, N) {
            int left = sum[k*off+l-1];
            int up = sum[(k-1)*off+l];
            int elt = a[k*off+l];
            int upleft = sum[(k-1)*off+l-1];
            sum[k*off+l] = left + up - upleft + elt;
        }
    }
    //------------------------------------------------------------------------------
    //   Perform algorithm (M - maksimum, u - upper, l - left, r - right, d - down)
    //------------------------------------------------------------------------------
    LLI Max = 0;
    LLI b1, b2, e1, e2, s, Min;
    int k, i, g; 
    LLI Min_ind = 0;
    for (k = myRank; k < M * M; k += numProcesses) {
        i = k % M + 1;
        g = k / M + 1;

        if (i < g) continue;

        off = N + 1; 
        Min = 0;
        FOR(l, 1, N) {
            s = sum[i * off + l] - sum[(g - 1) * off + l];
            cand = s - Min;
            if(cand > Max) {
                Max = cand;
                b1 = g;
                b2 = Min_ind + 1;
                e1 = i;
                e2 = l;
            }
            if(s < Min) {
                Min_ind = l;
                Min = s;
            }
        }
    }
    buffer[0] = Max;
    buffer[1] = b1;
    buffer[2] = b2;
    buffer[3] = e1;
    buffer[4] = e2;

    //------------------------------------------------------------------------------
    //   Receive results
    //------------------------------------------------------------------------------
     if (!myRank) {
        recvbuf = (LLI *) malloc(sizeof(LLI) * 5 * numProcesses);
        
        MPI_Gather(buffer, 5, MPI_LONG_LONG, recvbuf, 5, MPI_LONG_LONG, 0, MPI_COMM_WORLD);
        
        FOR(i, 1, numProcesses-1)
            if(buffer[0] < recvbuf[i * 5])
                REP(j, 5) buffer[j] = recvbuf[i * 5 + j]; 
    }

    //------------------------------------------------------------------------------
    //   Output
    //------------------------------------------------------------------------------
    if (!myRank) {
        endTime = MPI_Wtime();
        executionTime = endTime - startTime;

        fprintf(stderr, "PWIR2014_KonradLisiecki291649 Input: (%d,%d,%d) Solution: |(%d,%d),(%d,%d)|=%lld Time: %.10f\n",
            rows_no, columns_no, seed,
            (int)buffer[1], (int)buffer[2], (int)buffer[3], (int)buffer[4], buffer[0], executionTime);
    }

    //------------------------------------------------------------------------------
    //   Send results to main process
    //------------------------------------------------------------------------------
    if (myRank)
        MPI_Gather(buffer, 5, MPI_LONG_LONG, NULL, 5, MPI_LONG_LONG, 0, MPI_COMM_WORLD);

    MPI_Finalize();
    return 0;
}