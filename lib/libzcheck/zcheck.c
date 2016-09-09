/* 
 * LBC is a light-weight bounds checking compiler that instruments 
 * C program with runtime checks to ensure that no out-of-bounds sequential 
 * access is performed.
 * 
 * Copyright (C) 2008 - 2012 by Ashish Misra, Niranjan Hasabnis,
 * and R.Sekar in Secure Systems Lab, Stony Brook University, 
 * Stony Brook, NY 11794.
 * 
 * This program is free software; you can redistribute it and/or modify 
 * it under the terms of the GNU General Public License as published by 
 * the Free Software Foundation; either version 2 of the License, or 
 * (at your option) any later version. 
 * 
 * This program is distributed in the hope that it will be useful, 
 * but WITHOUT ANY WARRANTY; without even the implied warranty of 
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the 
 * GNU General Public License for more details. 
 * 
 * You should have received a copy of the GNU General Public License 
 * along with this program; if not, write to the Free Software 
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA.
 */

/*	
 *	The objective of this program is to provide the memory-checking routines.
 *	This file will be compiled in the form of a library.
 */

#include	"zcheck.h"

#include	<pthread.h>
#include	<stdlib.h>
#include	<assert.h>

#define 	NULL_PTR	((void *)0)

/*	
 *	The original calloc defined in glibc.
 */
void * glibc_calloc(size_t nmemb, size_t size);
void *memset(void *s, int c, size_t n);

//=============================================================================

/* 
 * There is already one in libc/malloc.c. Comment this
 * after due thought.
 */
 __thread unsigned type_size = 1;

// access lock for guard map.
extern pthread_mutex_t guard_map_acc_lock[MT_ARRAY_SIZE];

//=============================================================================
//	Note that for the time being we are forced to place this function in the
//	static library because of it requiring access to pthread functions. 
//
/*
 * Allocate a page inside guard map.
 * The index for which the page is to be allocated is 
 * determined by higher_index.
 */
void
alloc_guard_map_page(unsigned higher_index)
{
	unsigned lock_index;
	//	Lets get down first to the business of allocating the page.
	//=================================================================
	/*	Determine the lock to be used. We use the mod Prime-number
	 *	method to ensure uniform distribution	*/
	lock_index = higher_index % MT_ARRAY_SIZE;

	/*	This syntax has been picked up from malloc.c	*/
	(void) pthread_mutex_lock (& guard_map_acc_lock[lock_index]);

	/*	Note that we need to perform the check again because somebody
	 *	else may already have allocated the page while we were waiting
	 *	for it.	*/
	if (guard_map[higher_index] == 0) 
		if ((guard_map[higher_index] = 
			glibc_calloc (GZ_MAP_SIZE, sizeof(unsigned))) == 0)
			exit (1);

	(void) pthread_mutex_unlock(& guard_map_acc_lock[lock_index]);
}

/*
 * Check if the input pointer is pointing to guard zone
 * by looking up in the guard map.
 */
void 
is_guardzone(void * ptr)
{
/*	The basic idea of this macro is that we will return without executing any
 *	code. This will help us evaluate what is the overhead of just making the 
 *	call function and NOTHING ELSE.
 */
#ifdef	GZ_DUMMY_CHECK
	return; 
#else
/*	The basic objective here is to pass the pointer to the stack variable
 *	where the pointer is stored. Since the stack variable will always be the
 *	same, its address will be unique per function, that the compiler will
 *	hopefully and NOT use a register to compute it. This strategy is gonna
 *	results in lots of writes that MAY NOT matter. Will have to check.
 */
	unsigned index = (unsigned)ptr;

	unsigned higher_index = index >> GZ_HIGHER_ADDR_BITS;
	unsigned lower_index = (index & GZ_LOWER_ADDR_MSK) >> GZ_BIT_POSITION_BITS;
	unsigned bit_position = index & GZ_BIT_POS_MSK;

	if (guard_map[higher_index] != NULL_PTR)
		if (guard_map[higher_index][lower_index] &  (unsigned)(1 << bit_position))
			abort();

	return;
#endif
}


//=============================================================================
//    Functions related to marking and unmarking of guard zones.
//=============================================================================

#ifndef	GZ_TEST_MARKING

/*	The basic objective of this function is to mark the bits in the guard map
 *	with 1 from given address for given number of bytes.
 *	Note that now we will have three more invariants for these functions.
 *
 *	1.	The size of guardzones to be marked must be a multiple of 8 bytes.
 *	2.	The guardzones will be aligned on 8 byte boundaries.
 *	3.	The pages in guard map will be allocated a-priori. Checking for that is
 *		NOT the responsibility of this function.
 */
void 
mark_guardzone(void *address, unsigned int bit_count)
{	
	char * curr_addr = address;
	unsigned index = (unsigned)address;

	//	While we acknowledge that the guard map page is actually maintained as an
	//	array of unsigned ints, we will be accessing it as an array of
	//	unsigned characters.
	u_int32_t higher_index = (index >> GZ_HIGHER_ADDR_BITS);
	u_int32_t lower_index = (index & GZ_LOWER_CHAR_ADDR_MSK) >> GZ_NUMBER_OF_BITS;

	while(bit_count) {
		
		char *next_page_boundary = 
			(char *)((higher_index + 1) << GZ_HIGHER_ADDR_BITS);
		u_int32_t page_addr_remaining = (next_page_boundary - curr_addr);

		u_int32_t bits_to_set = (bit_count <= page_addr_remaining)? 
										bit_count : page_addr_remaining;

		//	Note that while we are measuring everything in terms of number of
		//	addresses that we will be setting, while supplying the value to
		//	memset, we must divide bits_to_set to get the number of bytes that
		//	memset will need to set.
		memset((( (char *)guard_map[higher_index]) + lower_index), 
				0xFF, (bits_to_set / 8));

		curr_addr = (char *)((++higher_index) << GZ_HIGHER_ADDR_BITS);
		lower_index = 0;
		bit_count -= bits_to_set;
	}
}

/*	The basic objective of this function is to unmark the bits in the guard map
 *	with 0 from given address for given number of bytes.
 *	Note that now we will now have three more invariants for these functions.
 *
 *	1.	The size of guardzones to be marked must be a multiple of 8 bytes.
 *	2.	The guardzones will be aligned on 8 byte boundaries.
 *	3.	The pages in guard map will be allocated a-priori. Checking for that is
 *		NOT the responsibility of this function.
 */
void 
unmark_guardzone(void *address, unsigned int bit_count)
{	
	char * curr_addr = address;
	unsigned index = (unsigned)address;

	//	While we acknowledge that the guard map page is actually maintained as an
	//	array of unsigned ints, we will be accessing it as an array of
	//	unsigned characters.
	u_int32_t higher_index = (index >> GZ_HIGHER_ADDR_BITS);
	u_int32_t lower_index = (index & GZ_LOWER_CHAR_ADDR_MSK) >> GZ_NUMBER_OF_BITS;

	while(bit_count) {
		
		char *next_page_boundary = 
			(char *)((higher_index + 1) << GZ_HIGHER_ADDR_BITS);
		u_int32_t page_addr_remaining = (next_page_boundary - curr_addr);

		u_int32_t bits_to_set = (bit_count <= page_addr_remaining)? 
										bit_count : page_addr_remaining;

		//	Note that while we are measuring everything in terms of number of
		//	addresses that we will be setting, while supplying the value to
		//	memset, we must divide bits_to_set to get the number of bytes that
		//	memset will need to set.
		memset( (((char *)guard_map[higher_index]) + lower_index), 
				0, (bits_to_set / 8));

		curr_addr = (char *)((++higher_index) << GZ_HIGHER_ADDR_BITS);
		lower_index = 0;
		bit_count -= bits_to_set;
	}
}

#else

void 
unmark_guardzone(void *address, unsigned int bit_count) {}

void 
mark_guardzone(void *address, unsigned int bit_count) {}

#endif	//	GZ_TEST_MARKING

