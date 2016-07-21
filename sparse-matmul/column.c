#include "column.h"
#include <string.h>

void do_column(void) {
    for (int i = 0; i < mpi_layer_size; ++i) {
        multiply_step();
    }

    double *tmp = dense_matrix;
    dense_matrix = result_matrix;
    result_matrix = tmp;

    memset(result_matrix, 0, (dense_col_range_end - dense_col_range_begin) *
                                 params.dimension * sizeof(double));
}
