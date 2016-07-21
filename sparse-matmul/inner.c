#include "inner.h"
#include <string.h>

static int num_phases;
static int my_coords[2];

static void prepare(void) {
    int prev, next;
    MPI_Status status;

    num_phases = mpi_layer_size / mpi_replication_group_size;
    REQUIRE(mpi_layer_size % mpi_replication_group_size == 0,
            "p/c^2 is not an integer");
    RUN(MPI_Cart_coords(mpi_cartesian_comm, mpi_my_rank, 2, my_coords));
    RUN(MPI_Cart_shift(mpi_cartesian_comm, 0, my_coords[1] * num_phases, &prev,
                       &next));
    RUN(MPI_Sendrecv(sparse_buffer->entries, sparse_buffer->count,
                     mpi_sparse_entry, next, SHIFT_TAG,
                     alternate_sparse_buffer->entries,
                     params.nnz * params.dimension, mpi_sparse_entry, prev,
                     SHIFT_TAG, mpi_cartesian_comm, &status));
    swap_buffers();
    RUN(MPI_Get_count(&status, mpi_sparse_entry, &sparse_buffer->count));
    REQUIRE(sparse_buffer->count != MPI_UNDEFINED, "MPI is broken");
}

static int real_dense_col_range_begin;
static int real_dense_col_range_end;
static int repl_group_rank;

static void replicate_dense(void) {
    real_dense_col_range_begin = dense_col_range_begin;
    real_dense_col_range_end = dense_col_range_end;

    dense_col_range_begin = my_coords[0] * rows_cols_per_replication_group();
    dense_col_range_end =
        (1 + my_coords[0]) * rows_cols_per_replication_group();
    if (dense_col_range_end > params.dimension) {
        dense_col_range_end = params.dimension;
    }
    if (dense_col_range_begin > dense_col_range_end) {
        dense_col_range_begin = dense_col_range_end;
    }

    dense_matrix = realloc(dense_matrix, rows_cols_per_replication_group() *
                                             params.dimension * sizeof(double));
    REQUIRE_ERRNO(dense_matrix, "Unable to reallocate the dense matrix");
    result_matrix =
        realloc(result_matrix, rows_cols_per_replication_group() *
                                   params.dimension * sizeof(double));
    REQUIRE_ERRNO(result_matrix, "Unable to reallocate the result matrix");

    MPI_Comm_rank(mpi_repl_group_comm, &repl_group_rank);
    if (repl_group_rank != 0) {
        memcpy(dense_matrix +
                   repl_group_rank * params.dimension * rows_cols_per_process(),
               dense_matrix,
               rows_cols_per_process() * params.dimension * sizeof(double));
    }

    RUN(MPI_Allgather(MPI_IN_PLACE, 0, MPI_DATATYPE_NULL, dense_matrix,
                      params.dimension * rows_cols_per_process(), MPI_DOUBLE,
                      mpi_repl_group_comm));

    memset(result_matrix, 0, (dense_col_range_end - dense_col_range_begin) *
                                 params.dimension * sizeof(double));
}

static void collect_dense(void) {
    /* TODO: ugly hack */
    RUN(MPI_Allreduce(MPI_IN_PLACE, dense_matrix,
                      rows_cols_per_replication_group() * params.dimension,
                      MPI_DOUBLE, MPI_SUM, mpi_repl_group_comm));
}

static void dereplicate_dense(void) {
    if (repl_group_rank != 0) {
        memcpy(dense_matrix,
               dense_matrix +
                   repl_group_rank * params.dimension * rows_cols_per_process(),
               rows_cols_per_process() * params.dimension * sizeof(double));
    }
}

void prepare_inner(void) {
    prepare();
    replicate_dense();
}

void finish_inner(void) {
    dereplicate_dense();
    dense_col_range_begin = real_dense_col_range_begin;
    dense_col_range_end = real_dense_col_range_end;
}

void do_inner(void) {
    for (int i = 0; i < num_phases; ++i) {
        multiply_step();
    }

    double *tmp = dense_matrix;
    dense_matrix = result_matrix;
    result_matrix = tmp;

    memset(result_matrix, 0, (dense_col_range_end - dense_col_range_begin) *
                                 params.dimension * sizeof(double));
    collect_dense();
}
