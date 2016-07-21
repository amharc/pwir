/*
 * A template for the 2016 Promela/SPIN Assignment at the University of Warsaw.
 * Copyright (C) 2016, Konrad Iwanicki.
 */
#ifndef TEST_FILE
#error This is not a test file to invoke spin on.
#endif // TEST_FILE

#ifndef RELIABLE_BROADCAST
#warning Using basic broadcast.
#endif // RELIABLE_BROADCAST

#include "mailboxes-impl.pml"


inline bb_pre_run_init()
{
    mb_init_pre();
}


inline bb_post_run_init()
{
    mb_init_post();
}


inline bb_broadcast(sm)
{
    int bb_broadcast_to;
    for (bb_broadcast_to : 0 .. NUM_PROCESSES - 1) {
        possibly_fail();
        mb_send(bb_broadcast_to, sm);
        possibly_fail();
    }
}


inline bb_deliver(rm)
{
    mb_recv(rm);
}
