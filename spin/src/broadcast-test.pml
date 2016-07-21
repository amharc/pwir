/*
 * A template for the 2016 Promela/SPIN Assignment at the University of Warsaw.
 * Copyright (C) 2016, Konrad Iwanicki.
 */
#define TEST_FILE

#ifndef NUM_PROCESSES
#define NUM_PROCESSES 1
#endif // NUM_PROCESSES

inline possibly_fail()
{
  atomic
  {
    if
    :: 1 -> skip
    :: 1 -> goto end_proc_fail
    fi
  }
}


#ifdef RELIABLE_BROADCAST

#include "reliable-broadcast-impl.pml"

#define pre_run_init() rb_pre_run_init()
#define post_run_init() rb_post_run_init()
#define broadcast(m) rb_broadcast(m)
#define deliver(m) rb_deliver(m)
#define continuation(m) rb_continuation(m)

#else

#include "basic-broadcast-impl.pml"

#define pre_run_init() bb_pre_run_init()
#define post_run_init() bb_post_run_init()
#define broadcast(m) bb_broadcast(m)
#define deliver(m) bb_deliver(m)
#define continuation(m)

#endif // RELIABLE_BROADCAST


#ifdef ONE_BROADCASTER

#define is_broadcaster(no) ((no + 1) == (ONE_BROADCASTER))
#define not_broadcaster(no) ((no + 1) != (ONE_BROADCASTER))

#else

#define is_broadcaster(no) (1)
#define not_broadcaster(no) (1)

#endif // ONE_BROADCASTER



proctype process(byte no)
{
  assert(_pid == no + 1 && no >= 0 && no < NUM_PROCESSES);
#ifdef RELIABLE_BROADCAST
  bit rb_dset[NUM_PROCESSES];
#endif // RELIABLE_BROADCAST
  byte sm = 0, rm = 0;
proc_started:
  possibly_fail();
  if
  :: d_step { not_broadcaster(no) -> skip }
  :: d_step { is_broadcaster(no) -> sm = no + 1 }
proc_broadcast:
     broadcast(sm)
  fi;
  possibly_fail();
  do
  :: 1 ->
proc_await_message:
     deliver(rm);
proc_deliver:
     possibly_fail();
#ifdef RELIABLE_BROADCAST
proc_cont:
     continuation(rm);
     possibly_fail();
#endif // RELIABLE_BROADCAST
     rm = 0
  od;
end_proc_fail:
  0
}


init
{
  atomic
  {
    byte i;
    pre_run_init();
    i = 0;
    do
    :: i < NUM_PROCESSES ->
       run process(i);
       i++
    :: else ->
       break    
    od;
    post_run_init();
    i = 0
  }
}


#include "broadcast-ltl.pml"
