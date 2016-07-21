#include "common.h"
#include "densematgen.h"
#include <assert.h>
#include <string.h>

struct sparse_matrix *read_sparse(const char *filename) {
    FILE *filp;
    REQUIRE_ERRNO(filp = fopen(filename, "r"), "Unable to open file");

    int ncols, nrows, nnz, maxnz;
    REQUIRE_ERRNO(4 == fscanf(filp, "%d%d%d%d", &ncols, &nrows, &nnz, &maxnz),
                  "Unable to process the first row of the sparse matrix file");

    REQUIRE(ncols == nrows,
            "Only square matrices are supported, but %dx%d provided", ncols,
            nrows);

    struct sparse_matrix *matrix = malloc(sizeof(struct sparse_matrix) +
                                          nnz * sizeof(struct sparse_entry));
    REQUIRE_ERRNO(matrix, "Unable to allocate memory for the sparse matrix");

    matrix->params.dimension = ncols;
    matrix->params.nnz = nnz;
    matrix->params.maxnz = maxnz;
    for (int i = 0; i < nnz; ++i) {
        REQUIRE_ERRNO(1 == fscanf(filp, "%lf", &matrix->entries[i].entry),
                      "Unable to read the %d-th matrix entry", i);
    }

    {
        int idx;
        REQUIRE_ERRNO(1 == fscanf(filp, "%d", &idx),
                      "Unable to read the first element of the IA array");
        REQUIRE(idx == 0, "The first element of the IA array must be zero");
        for (int row = 0; row < nrows; ++row) {
            int newidx;
            REQUIRE_ERRNO(1 == fscanf(filp, "%d", &newidx),
                          "Unable to read the %d-ith element of the IA array",
                          row);
            REQUIRE(newidx >= idx, "The IA array is not nondecreasing: %d > %d",
                    idx, newidx);
            REQUIRE(newidx <= nnz,
                    "An element of the IA array exceeds bounds: %d > nnz=%d",
                    newidx, nnz);
            while (idx < newidx) {
                matrix->entries[idx].row = row;
                ++idx;
            }
        }
    }

    for (int i = 0; i < nnz; ++i) {
        REQUIRE_ERRNO(1 == fscanf(filp, "%d", &matrix->entries[i].col),
                      "Unable to read the %d-th JA array entry", i);
        REQUIRE(matrix->entries[i].col >= 0,
                "Negative column of the %d-the entry", i);
        REQUIRE(matrix->entries[i].col < ncols,
                "Invalid column of the %d-the entry: %d < %d", i,
                matrix->entries[i].col, ncols);
    }

    REQUIRE_ERRNO(0 == fclose(filp), "Unable to close file");

    return matrix;
}

void free_sparse(struct sparse_matrix *matrix) {
    free(matrix);
}

MPI_Datatype mpi_sparse_entry;
static void initialize_mpi_sparse_entry(void) {
    int blocklengths[] = {1, 1, 1};
    MPI_Datatype types[] = {MPI_INT, MPI_INT, MPI_DOUBLE};
    MPI_Aint offsets[] = {offsetof(struct sparse_entry, row),
                          offsetof(struct sparse_entry, col),
                          offsetof(struct sparse_entry, entry)};

    MPI_Datatype tmp;
    RUN(MPI_Type_create_struct(3, blocklengths, offsets, types,
                               &tmp));
    RUN(MPI_Type_create_resized(tmp, 0, sizeof(struct sparse_entry), &mpi_sparse_entry));
    RUN(MPI_Type_commit(&mpi_sparse_entry));
}

static void free_mpi_sparse_entry(void) {
    RUN(MPI_Type_free(&mpi_sparse_entry));
}

MPI_Datatype mpi_params;
static void initialize_mpi_params(void) {
    int blocklengths[] = {1, 1, 1, 1};
    MPI_Datatype types[] = {MPI_INT, MPI_INT, MPI_INT, MPI_INT};
    MPI_Aint offsets[] = {
        offsetof(struct params, dimension), offsetof(struct params, nnz),
        offsetof(struct params, maxnz),
        offsetof(struct params, max_sparse_entries_per_process)};

    MPI_Datatype tmp;
    RUN(MPI_Type_create_struct(4, blocklengths, offsets, types, &tmp));
    RUN(MPI_Type_create_resized(tmp, 0, sizeof(struct params), &mpi_params));
    RUN(MPI_Type_commit(&mpi_params));
}

static void free_mpi_params(void) {
    RUN(MPI_Type_free(&mpi_params));
}

MPI_Comm mpi_cartesian_comm;
int mpi_my_rank;
int mpi_prev_in_layer;
int mpi_next_in_layer;
static void initialize_mpi_cartesian_comm(void) {
    int dims[] = {mpi_layer_size, mpi_replication_group_size};
    int periods[] = {1, 0};
    RUN(MPI_Cart_create(MPI_COMM_WORLD, 2, dims, periods, 1,
                        &mpi_cartesian_comm));
    RUN(MPI_Comm_rank(mpi_cartesian_comm, &mpi_my_rank));
    RUN(MPI_Cart_shift(mpi_cartesian_comm, 0, 1, &mpi_prev_in_layer,
                       &mpi_next_in_layer));
}

MPI_Comm mpi_repl_group_comm;
static void initialize_mpi_repl_group_comm(void) {
    int remain_dims[] = {0, 1};
    RUN(MPI_Cart_sub(mpi_cartesian_comm, remain_dims, &mpi_repl_group_comm));
}

int mpi_replication_group_size;
int mpi_layer_size;
int mpi_num_processes;
void initialize_mpi(int c) {
    MPI_Comm_size(MPI_COMM_WORLD, &mpi_num_processes);
    mpi_replication_group_size = c;
    mpi_layer_size = mpi_num_processes / c;
    REQUIRE(mpi_layer_size * mpi_replication_group_size == mpi_num_processes,
            "Number of processes must be divisible by the replication factor");

    initialize_mpi_sparse_entry();
    initialize_mpi_params();

    initialize_mpi_cartesian_comm();
    initialize_mpi_repl_group_comm();
}

void free_mpi(void) {
    RUN(MPI_Comm_free(&mpi_repl_group_comm));
    RUN(MPI_Comm_free(&mpi_cartesian_comm));
    free_mpi_sparse_entry();
    free_mpi_params();

    free(sparse_buffer);
    sparse_buffer = NULL;

    free(alternate_sparse_buffer);
    alternate_sparse_buffer = NULL;

    free(dense_matrix);
    dense_matrix = NULL;

    free(result_matrix);
    result_matrix = NULL;
}

struct sparse_buffer *sparse_buffer;
struct sparse_buffer *alternate_sparse_buffer;
static void alloc_sparse_buffer(int elems, struct sparse_buffer **buffer) {
    *buffer = calloc(1, sizeof(struct sparse_buffer) +
                            elems * sizeof(struct sparse_entry) + 200);
    REQUIRE_ERRNO(*buffer, "Unable to allocate a buffer for the sparse matrix");
    (*buffer)->count = 0;
}

void alloc_sparse_buffers(int elems) {
    alloc_sparse_buffer(elems, &sparse_buffer);
    alloc_sparse_buffer(elems, &alternate_sparse_buffer);
}

inline void swap_buffers(void) {
    struct sparse_buffer *buffer = sparse_buffer;
    sparse_buffer = alternate_sparse_buffer;
    alternate_sparse_buffer = buffer;
}

struct params params;
void scatter_sparse(const struct sparse_matrix *matrix, splitter_t splitter) {
    if (mpi_my_rank == 0) {
        assert(matrix);
        params = matrix->params;

        int *counts = calloc(mpi_num_processes, sizeof(int));
        REQUIRE_ERRNO(counts, "Unable to allocate memory");

        int *displacements = calloc(mpi_num_processes, sizeof(int));
        REQUIRE_ERRNO(displacements, "Unable to allocate memory");

        int *temp = calloc(mpi_num_processes, sizeof(int));
        REQUIRE_ERRNO(temp, "Unable to allocate memory");

        struct sparse_entry *entries =
            calloc(matrix->params.nnz, sizeof(struct sparse_entry));
        REQUIRE_ERRNO(entries, "Unable to allocate memory");

        /* Counting sort */
        for (int i = 0; i < matrix->params.nnz; ++i) {
            int where = splitter(&matrix->entries[i]);
            assert(where >= 0 && where < mpi_num_processes);
            counts[where]++;
        }

        int maxcount = 0;

        {
            int total = 0;
            for (int i = 0; i < mpi_num_processes; ++i) {
                temp[i] = displacements[i] = total;
                total += counts[i];
                if (counts[i] > maxcount) {
                    maxcount = counts[i];
                }
            }
        }

        for (int i = 0; i < matrix->params.nnz; ++i) {
            int where = splitter(&matrix->entries[i]);
            entries[temp[where]] = matrix->entries[i];
            temp[where]++;
        }

        params.max_sparse_entries_per_process =
            mpi_replication_group_size * maxcount;

        RUN(MPI_Bcast(&params, 1, mpi_params, 0, mpi_cartesian_comm));
        alloc_sparse_buffers(params.max_sparse_entries_per_process);

        RUN(MPI_Scatter(counts, 1, MPI_INT, &sparse_buffer->count, 1, MPI_INT,
                        0, mpi_cartesian_comm));
        RUN(MPI_Scatterv(entries, counts, displacements, mpi_sparse_entry,
                         sparse_buffer->entries, counts[0], mpi_sparse_entry, 0,
                         mpi_cartesian_comm));

        free(counts);
        free(displacements);
        free(temp);
        free(entries);
    } else {
        RUN(MPI_Bcast(&params, 1, mpi_params, 0, mpi_cartesian_comm));
        alloc_sparse_buffers(params.max_sparse_entries_per_process);
        RUN(MPI_Scatter(MPI_BOTTOM, 0, MPI_DATATYPE_NULL, &sparse_buffer->count,
                        1, MPI_INT, 0, mpi_cartesian_comm));
        RUN(MPI_Scatterv(MPI_BOTTOM, MPI_BOTTOM, MPI_BOTTOM, MPI_DATATYPE_NULL,
                         sparse_buffer->entries, sparse_buffer->count,
                         mpi_sparse_entry, 0, mpi_cartesian_comm));
    }
}

void replicate_sparse(void) {
    int *counts = calloc(mpi_replication_group_size, sizeof(int));
    REQUIRE_ERRNO(counts, "Unable to allocate memory");
    RUN(MPI_Allgather(&sparse_buffer->count, 1, MPI_INT, counts, 1, MPI_INT,
                      mpi_repl_group_comm));

    int *displacements = calloc(mpi_replication_group_size, sizeof(int));
    REQUIRE_ERRNO(displacements, "Unable to allocate memory");

    for (int i = 1; i < mpi_replication_group_size; ++i) {
        displacements[i] = displacements[i - 1] + counts[i - 1];
    }

    int total = displacements[mpi_replication_group_size - 1] +
                counts[mpi_replication_group_size - 1];

    REQUIRE(total <= params.max_sparse_entries_per_process,
            "My internal size bookkeeping just went terribly wrong");

    swap_buffers();

    RUN(MPI_Allgatherv(alternate_sparse_buffer->entries,
                       alternate_sparse_buffer->count, mpi_sparse_entry,
                       sparse_buffer->entries, counts, displacements,
                       mpi_sparse_entry, mpi_repl_group_comm));
    sparse_buffer->count = total;

    free(displacements);
    free(counts);
}

MPI_Request mpi_requests[2];
inline void shift_sparse(void) {
    RUN(MPI_Isend(sparse_buffer->entries, sparse_buffer->count,
                  mpi_sparse_entry, mpi_next_in_layer, SHIFT_TAG,
                  mpi_cartesian_comm, &mpi_requests[0]));
    RUN(MPI_Irecv(alternate_sparse_buffer->entries,
                  params.max_sparse_entries_per_process, mpi_sparse_entry,
                  mpi_prev_in_layer, SHIFT_TAG, mpi_cartesian_comm,
                  &mpi_requests[1]));
}

inline void finish_shift(void) {
    MPI_Status mpi_statuses[2];
    RUN(MPI_Waitall(2, mpi_requests, mpi_statuses));
    swap_buffers();
    RUN(MPI_Get_count(&mpi_statuses[1], mpi_sparse_entry,
                      &sparse_buffer->count));
    REQUIRE(sparse_buffer->count != MPI_UNDEFINED, "MPI is broken");
}

int dense_col_range_begin;
int dense_col_range_end;
static void allocate_dense(double **matrix) {
    *matrix =
        calloc(params.dimension * rows_cols_per_process(), sizeof(double));
    REQUIRE_ERRNO(*matrix, "Cannot allocate memory");
}

double *dense_matrix;
double *result_matrix;
void initialise_dense(int seed) {
    int cols_per_process =
        (params.dimension + mpi_num_processes - 1) / mpi_num_processes;
    dense_col_range_begin = cols_per_process * mpi_my_rank;
    dense_col_range_end = cols_per_process * (1 + mpi_my_rank);
    if (dense_col_range_end > params.dimension) {
        dense_col_range_end = params.dimension;
    }
    if (dense_col_range_begin > dense_col_range_end) {
        dense_col_range_begin = dense_col_range_end;
    }

    allocate_dense(&dense_matrix);
    allocate_dense(&result_matrix);

    for (int col = dense_col_range_begin; col < dense_col_range_end; ++col) {
        for (int row = 0; row < params.dimension; ++row) {
            MATRIX(dense, row, col) = generate_double(seed, row, col);
        }
    }
}

double *gather_dense(void) {
    if (mpi_my_rank == 0) {
        int size =
            rows_cols_per_process() * mpi_num_processes * params.dimension;
        double *full_matrix = calloc(size, sizeof(double));
        REQUIRE_ERRNO(full_matrix, "Unable to allocate memory");
        RUN(MPI_Gather(dense_matrix, rows_cols_per_process() * params.dimension,
                       MPI_DOUBLE, full_matrix,
                       rows_cols_per_process() * params.dimension, MPI_DOUBLE,
                       0, mpi_cartesian_comm));
        return full_matrix;
    } else {
        RUN(MPI_Gather(dense_matrix, rows_cols_per_process() * params.dimension,
                       MPI_DOUBLE, MPI_BOTTOM, 0, MPI_DATATYPE_NULL, 0,
                       mpi_cartesian_comm));
        return NULL;
    }
}

int count_greater_equal(double threshold) {
    int ret = -1;
    int count = 0;
    for (int col = dense_col_range_begin; col < dense_col_range_end; ++col) {
        for (int row = 0; row < params.dimension; ++row) {
            if (MATRIX(dense, row, col) >= threshold) {
                count++;
            }
        }
    }
    RUN(MPI_Reduce(&count, &ret, 1, MPI_INT, MPI_SUM, 0, mpi_cartesian_comm));
    return ret;
}

void multiply_step(void) {
#ifdef PROFILE
    double start = MPI_Wtime();
#endif
    shift_sparse();
#ifdef PROFILE
    double comp_start = MPI_Wtime();
#endif
    for (int col = dense_col_range_begin; col < dense_col_range_end; ++col) {
        for (int i = 0; i < sparse_buffer->count; ++i) {
            MATRIX(result, sparse_buffer->entries[i].row, col) +=
                sparse_buffer->entries[i].entry *
                MATRIX(dense, sparse_buffer->entries[i].col, col);
        }
    }
#ifdef PROFILE
    double comp_end = MPI_Wtime();
#endif
    finish_shift();
#ifdef PROFILE
    double end = MPI_Wtime();
    printf("Process %d: %f spent in multiply_step\n", mpi_my_rank, end - start);
    printf("Process %d: %f spent multiplying in multiply_step\n", mpi_my_rank,
           comp_end - comp_start);
#endif
}
