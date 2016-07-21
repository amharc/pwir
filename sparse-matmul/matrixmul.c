#include <assert.h>
#include <getopt.h>
#include <mpi.h>
#include <stdio.h>
#include <stdlib.h>

#include "column.h"
#include "common.h"
#include "inner.h"

#include "densematgen.h"

static struct algorithm {
    void (*prepare)(void);
    void (*run)(void);
    void (*finish)(void);
} column = {.prepare = NULL, .run = do_column, .finish = NULL},
  inner = {.prepare = prepare_inner, .run = do_inner, .finish = finish_inner};

int main(int argc, char *argv[]) {
    int show_results = 0;
    int use_inner = 0;
    int gen_seed = -1;
    int repl_fact = 1;

    int option = -1;

    double comm_start = 0, comm_end = 0, comp_start = 0, comp_end = 0;
    int exponent = 1;
    double ge_element = 0;
    int count_ge = 0;

    struct sparse_matrix *sparse = NULL;

    MPI_Init(&argc, &argv);
    MPI_Comm_rank(MPI_COMM_WORLD, &mpi_my_rank);

    while ((option = getopt(argc, argv, "vis:f:c:e:g:")) != -1) {
        switch (option) {
        case 'v':
            show_results = 1;
            break;
        case 'i':
            use_inner = 1;
            break;
        case 'f':
            if ((mpi_my_rank) == 0) {
                sparse = read_sparse(optarg);
            }
            break;
        case 'c':
            repl_fact = atoi(optarg);
            break;
        case 's':
            gen_seed = atoi(optarg);
            break;
        case 'e':
            exponent = atoi(optarg);
            break;
        case 'g':
            count_ge = 1;
            ge_element = atof(optarg);
            break;
        default:
            fprintf(stderr, "error parsing argument %c exiting\n", option);
            MPI_Finalize();
            return 3;
        }
    }
    if ((gen_seed == -1) || ((mpi_my_rank == 0) && (sparse == NULL))) {
        fprintf(stderr, "error: missing seed or sparse matrix file; exiting\n");
        MPI_Finalize();
        return 3;
    }

    initialize_mpi(repl_fact);

    struct algorithm alg = use_inner ? inner : column;

    comm_start = MPI_Wtime();
    scatter_sparse(sparse, use_inner ? row_splitter : column_splitter);
    if (sparse) {
        free_sparse(sparse);
    }
    replicate_sparse();
    initialise_dense(gen_seed);
    if (alg.prepare)
        alg.prepare();
    MPI_Barrier(MPI_COMM_WORLD);
    comm_end = MPI_Wtime();
    comp_start = MPI_Wtime();
    for (int i = 0; i < exponent; ++i) {
        alg.run();
    }
    if (alg.finish)
        alg.finish();
    MPI_Barrier(MPI_COMM_WORLD);
    comp_end = MPI_Wtime();

    if (show_results) {
        double *matrix = gather_dense();
        if (matrix) {
            printf("%1$d %1$d\n", params.dimension);
            for (int row = 0; row < params.dimension; ++row) {
                for (int col = 0; col < params.dimension; ++col) {
                    printf("%10.5f ", matrix[col * params.dimension + row]);
                }
                printf("\n");
            }
            free(matrix);
        }
    }
    if (count_ge) {
        int count = count_greater_equal(ge_element);
        if (count != -1) {
            printf("%d\n", count);
        }
    }

    free_mpi();
    MPI_Finalize();
    return 0;
}
