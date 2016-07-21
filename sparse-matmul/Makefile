CC      = mpicc
CFLAGS  = -Wall -c --std=gnu11 -O3 -flto
LDFLAGS = -Wall --std=gnu11 -O3 -flto
ALL     = matrixmul
MATGENFILE = densematgen.o

SOURCES=$(wildcard *.c)
DEPENDS=$(patsubst %.c,.%.depends,$(SOURCES))
OBJECTS=$(patsubst %.c,%.o,$(SOURCES))

all: $(ALL)
matrixmul: matrixmul.o $(OBJECTS)

.%.depends: %.c
	$(CC) $(CFLAGS) -MM $< -o $@

.PHONY: clean
clean:
	rm -f *.o *core *~ *.out *.err $(ALL)

-include $(DEPENDS)
