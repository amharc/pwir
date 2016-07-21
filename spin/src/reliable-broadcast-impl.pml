/*
 * A template for the 2016 Promela/SPIN Assignment at the University of Warsaw.
 * Copyright (C) 2016, Konrad Iwanicki.
 */
#ifndef TEST_FILE
#error This is not a test file to invoke spin on.
#endif // TEST_FILE

#warning Using reliable broadcast.


#include "basic-broadcast-impl.pml"


inline rb_pre_run_init()
{
    bb_pre_run_init();
}


inline rb_post_run_init()
{
    bb_post_run_init();
}


inline rb_broadcast(sm)
{
    bb_broadcast(sm);
}


inline rb_deliver(rm)
{
    do
    :: bb_deliver(rm) ->
       if
       :: rb_dset[rm - 1] -> skip;
       :: else -> break;
       fi;
    od;

    rb_dset[rm - 1] = true;
}


inline rb_continuation(rm)
{
    bb_broadcast(rm);
}
