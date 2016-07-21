/*
 * A template for the 2016 Promela/SPIN Assignment at the University of Warsaw.
 * Copyright (C) 2016, Konrad Iwanicki.
 */
#define TEST_FILE

#ifndef NUM_PROCESSES
#define NUM_PROCESSES 1
#endif // NUM_PROCESSES

#ifdef ONE_SENDER
#define is_sender(no) ((no + 1) == (ONE_SENDER))
#define not_sender(no) ((no + 1) != (ONE_SENDER))
#else
#define is_sender(no) (1)
#define not_sender(no) (1)
#endif // ONE_SENDER

#ifdef ONE_RECEIVER
#define select_receiver(r) r = (ONE_RECEIVER)
#else
#define select_receiver(r) rand_recipient(r)
#endif // ONE_RECEIVER


#include "mailboxes-impl.pml"


inline rand_recipient(i)
{
  /* executed from within an atomic block */
  i = 1;
  do
  :: i < NUM_PROCESSES -> i++
  :: 1 -> break
  od
}


proctype proc(byte no)
{
  assert(_pid == no + 1 && no >= 0 && no < NUM_PROCESSES);
  byte sm = 0, rm = 0, tp = 0;
proc_started:
  if
  :: d_step { not_sender(no) -> skip }
  :: atomic { is_sender(no) -> sm = no + 1; select_receiver(tp) }
proc_send:
     mb_send(tp - 1, sm)
  fi;
proc_done:
  do
  :: 1 ->
end_proc_await:
     mb_recv(rm);
proc_receive:
     rm = 0
  od
}


init
{
  atomic
  {
    byte i;
    mb_init_pre();
    i = 0;
    do
      :: i < NUM_PROCESSES ->
         run proc(i);
         i++
      :: else ->
         break
    od;
    mb_init_post();
    i = 0
  }
}


#include "mailboxes-ltl.pml"
