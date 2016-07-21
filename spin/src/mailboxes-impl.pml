/*
 * A template for the 2016 Promela/SPIN Assignment at the University of Warsaw.
 * Copyright (C) 2016, Konrad Iwanicki.
 */
#ifndef TEST_FILE
#error This is not a test file to invoke spin on.
#endif // TEST_FILE

chan queues[NUM_PROCESSES] = [255] of { byte };

inline mb_init_pre()
{
  // FIXME: implement
  skip
}


inline mb_init_post()
{
  // FIXME: implement
  skip
}


inline mb_send(rmbi, m)
{
    queues[rmbi] ! m;
}


inline mb_recv(m)
{
    queues[_pid - 1] ? m;
}
