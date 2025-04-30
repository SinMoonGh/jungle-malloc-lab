#
# Students' Makefile for the Malloc Lab
#
TEAM = bovik
VERSION = 1
HANDINDIR = /afs/cs.cmu.edu/academic/class/15213-f01/malloclab/handin

CC = gcc
# CFLAGS = -Wall -O2 -m32
CFLAGS = -Wall -O2 -g

OBJS = mdriver.o mm.o memlib.o fsecs.o fcyc.o clock.o ftimer.o

# mdriver
mdriver: $(OBJS)
	$(CC) $(CFLAGS) -o mdriver $(OBJS)

# 추가
mm_test: mm_test.o mm.o memlib.o
	$(CC) $(CFLAGS) -o mm_test mm_test.o mm.o memlib.o

# mdriver 실행에 필요한 오브젝트 파일들
mdriver.o: mdriver.c fsecs.h fcyc.h clock.h memlib.h config.h mm.h
memlib.o: memlib.c memlib.h
mm.o: mm.c mm.h memlib.h
fsecs.o: fsecs.c fsecs.h config.h
fcyc.o: fcyc.c fcyc.h
ftimer.o: ftimer.c ftimer.h config.h
clock.o: clock.c clock.h

# mm_test에 필요한 오브젝트 파일
mm_test.o: mm_test.c mm.h memlib.h

handin:
	cp mm.c $(HANDINDIR)/$(TEAM)-$(VERSION)-mm.c

clean:
	rm -f *~ *.o mdriver
