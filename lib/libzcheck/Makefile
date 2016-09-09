# LBC is a light-weight bounds checking compiler that instruments 
# C program with runtime checks to ensure that no out-of-bounds sequential 
# access is performed.
# 
# Copyright (C) 2008 - 2012 by Ashish Misra, Niranjan Hasabnis,
# and R.Sekar in Secure Systems Lab, Stony Brook University, 
# Stony Brook, NY 11794.
# 
# This program is free software; you can redistribute it and/or modify 
# it under the terms of the GNU General Public License as published by 
# the Free Software Foundation; either version 2 of the License, or 
# (at your option) any later version. 
# 
# This program is distributed in the hope that it will be useful, 
# but WITHOUT ANY WARRANTY; without even the implied warranty of 
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the 
# GNU General Public License for more details. 
# 
# You should have received a copy of the GNU General Public License 
# along with this program; if not, write to the Free Software 
# Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA.

CC = gcc
AR = ar
CFLAGS = -O2

libzcheck.a: zcheck.o
	$(AR) rcs $@ $<

zcheck.o: zcheck.c ../../include/zcheck.h
	$(CC) $(CFLAGS) -I../../include -c zcheck.c

all: libzcheck.a

clean:
	rm -f *.o libzcheck.a


