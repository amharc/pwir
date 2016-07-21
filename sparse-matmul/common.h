#pragma once

#include <mpi.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

/** Stringification of the current line. Yay, cpp... */
#define STR(X) #X
#define STR2(X) STR(X)
#define STR_LINE STR2(__LINE__)

#define REQUIRE(condition, message, ...)                                       \
    do {                                                                       \
        if (!(condition)) {                                                    \
            fprintf(stderr,                                                    \
                    "Error. %s is not satisfied at " __FILE__ ":" STR_LINE     \
                    "\nFunction: %s\nMessage: " message "\n",                  \
                    #condition, __PRETTY_FUNCTION__, ##__VA_ARGS__);           \
            exit(EXIT_FAILURE);                                                \
        }                                                                      \
    } while (0)

#define REQUIRE_ERRNO(condition, message, ...)                                 \
    REQUIRE(condition, message "\nerrno: %m", ##__VA_ARGS__)

#ifndef PROFILE
#define RUN(command) REQUIRE(MPI_SUCCESS == (command), "Huh...")
#else
#define RUN(command)                                                           \
    do {                                                                       \
        double start = MPI_Wtime();                                            \
        REQUIRE(MPI_SUCCESS == (command), "Huh...");                           \
        double end = MPI_Wtime();                                              \
        printf("Process %d: %f spent in %s\n", mpi_my_rank, end - start,       \
               #command);                                                      \
    } while (0)
#endif

#define SHIFT_TAG 42

struct sparse_entry {
    int row, col;
    double entry;
};

struct params {
    int dimension, nnz, maxnz, max_sparse_entries_per_process;
};

struct sparse_matrix {
    struct params params;
    struct sparse_entry entries[];
};

struct sparse_matrix *read_sparse(const char *filename);
void free_sparse(struct sparse_matrix *matrix);
void initialize_mpi(int c);
void free_mpi(void);

extern MPI_Datatype mpi_sparse_entry;
extern MPI_Datatype mpi_params;
extern MPI_Comm mpi_cartesian_comm;
extern MPI_Comm mpi_repl_group_comm;
extern int mpi_replication_group_size;
extern int mpi_layer_size;
extern int mpi_my_rank;
extern int mpi_num_processes;
extern struct params params;
extern int mpi_prev_in_layer;
extern int mpi_next_in_layer;
extern double *dense_matrix;
extern double *result_matrix;
extern int dense_col_range_begin;
extern int dense_col_range_end;

#define MATRIX(name, row, col)                                                 \
    (name##_matrix[((col)-dense_col_range_begin) * params.dimension + (row)])

struct sparse_buffer {
    int count;
    struct sparse_entry entries[];
};

extern struct sparse_buffer *sparse_buffer;
extern struct sparse_buffer *alternate_sparse_buffer;
void alloc_sparse_buffers(int elems);
void swap_buffers(void);

typedef int (*splitter_t)(const struct sparse_entry *);

__attribute__((pure)) static inline int rows_cols_per_process() {
    return (params.dimension + mpi_num_processes - 1) / mpi_num_processes;
}

__attribute__((pure)) static inline int rows_cols_per_replication_group() {
    return rows_cols_per_process() * mpi_replication_group_size;
}

__attribute__((pure)) static inline int
column_splitter(const struct sparse_entry *entry) {
    return entry->col / rows_cols_per_process();
}

__attribute__((pure)) static inline int
row_splitter(const struct sparse_entry *entry) {
    return entry->row / rows_cols_per_process();
}

void scatter_sparse(const struct sparse_matrix *matrix, splitter_t splitter);

void replicate_sparse(void);
void shift_sparse(void);
void finish_shift(void);
void initialise_dense(int seed);

double *gather_dense(void);
int count_greater_equal(double threshold);
void multiply_step(void);
