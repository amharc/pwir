/*
 * A template for the 2016 Promela/SPIN Assignment at the University of Warsaw.
 * Copyright (C) 2016, Konrad Iwanicki.
 */
#ifndef TEST_FILE
#error This is not a test file to invoke spin on.
#endif // TEST_FILE

#define CORRECT(who) ([](!process[who]@end_proc_fail))
#define DELIVERED(who, msg) ((process[who]@proc_deliver) && (process[who]:rm == msg))
#define BROADCAST(who, msg) ((process[who]@proc_broadcast) && (process[who]:sm == msg))
#define NEVER_DELIVERED(who, msg) (!<>DELIVERED(who, msg))
#define NO_DUPLICATION(who, msg) ([]((DELIVERED(who, msg)) -> [](process[who]@proc_broadcast -> NEVER_DELIVERED(who, msg))))
#define NO_CREATION(who, sender, msg) ((!DELIVERED(who, msg)) W (BROADCAST(sender, msg)))
#define IF_BROADCAST_THEN_DELIVERED(who, sender, msg) ([](BROADCAST(sender, msg) -> <>DELIVERED(who, msg)))
#define WEAK_VALIDITY(who, msg) (CORRECT(who) -> IF_BROADCAST_THEN_DELIVERED(who, who, msg))
#define STRONG_VALIDITY(who, sender, msg) ((CORRECT(sender) && CORRECT(who)) -> IF_BROADCAST_THEN_DELIVERED(who, sender, msg))
#define IF_DELIVERED_THEN_DELIVERED(who, first, msg) ((<>DELIVERED(first, msg)) -> (<>DELIVERED(who, msg)))
#define WEAK_AGREEMENT(who, other, msg) ((CORRECT(who) && CORRECT(other)) -> IF_DELIVERED_THEN_DELIVERED(who, other, msg))
#define STRONG_AGREEMENT(who, other, msg) ((CORRECT(who)) -> IF_DELIVERED_THEN_DELIVERED(who, other, msg))

ltl no_duplication { NO_DUPLICATION(RECEIVER, SENDER) }

ltl no_creation { NO_CREATION(RECEIVER, SENDER, SENDER) }

ltl weak_validity { WEAK_VALIDITY(SENDER, SENDER) }

ltl strong_validity { STRONG_VALIDITY(RECEIVER, SENDER, SENDER) }

ltl weak_agreement { WEAK_AGREEMENT(RECEIVER, THIRD, SENDER) }

ltl strong_agreement { STRONG_AGREEMENT(RECEIVER, THIRD, SENDER) }
