/*
 * A template for the 2016 Promela/SPIN Assignment at the University of Warsaw.
 * Copyright (C) 2016, Konrad Iwanicki.
 */
#ifndef TEST_FILE
#error This is not a test file to invoke spin on.
#endif // TEST_FILE

#define SEND(x, y, msg) ((proc[x]@proc_send) && (proc[x]:sm == msg) && (proc[x]:tp == y))
#define RECEIVE(x, msg) (proc[x]@proc_receive && (proc[x]:rm == msg))
#define RECEIVES_INFINITELY_OFTEN(x) ([]<>proc[x]@proc_receive)
#define GUARANTEED_DELIVERY(from, to, msg) ([]((SEND(from, to, msg) && RECEIVES_INFINITELY_OFTEN(to)) -> RECEIVE(to, msg)))
#define AT_MOST_ONCE_DELIVERY(to, msg) ([](RECEIVE(to, msg) -> ([](proc[to]@end_proc_await -> !(<>RECEIVE(to, msg))))))
#define NO_FABRICATION(from, to, msg) ((!RECEIVE(to, msg)) W (SEND(from, to, msg)))

ltl mb_guaranteed_delivery { GUARANTEED_DELIVERY(1, 2, 1) && GUARANTEED_DELIVERY(1, 1, 1) }

ltl mb_at_most_once_delivery { AT_MOST_ONCE_DELIVERY(1, 2) && AT_MOST_ONCE_DELIVERY(1, 1) }

ltl mb_no_fabrication { NO_FABRICATION(1, 2, 1) && NO_FABRICATION(1, 1, 1) }
