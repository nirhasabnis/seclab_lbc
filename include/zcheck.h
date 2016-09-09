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

#ifndef	ZCHECK_H
#define	ZCHECK_H

//=============================================================================

/*	The objective of this section is to include the function prototypes of the
 *	std c functions. Directly include the header files creates problems during
 *	transformation and should be avoided
 */

static int printf(const char *format, ...);
void abort(void);

//=============================================================================
 
#define GZ_TRUE 	1
#define GZ_FALSE 	0

/* 
 * Number of bits that determine the index into first-level array of guard map.
 */
#define	GZ_HIGHER_ADDR_BITS 		16

/* 
 * Number of bits that determine the index into map page.
 */
#define GZ_LOWER_ADDR_BITS 			11
#define GZ_BIT_POSITION_BITS		5
#define	GZ_NUMBER_OF_BITS			3

#define GZ_LOWER_ADDR_MSK 		0x0000ffe0
#define GZ_BIT_POS_MSK			0x0000001f
 
/*	If we want to consider the guardmap page as an array of characters, then
 *	these are the values that we need to use as mask and lower index.
 */
#define GZ_LOWER_CHAR_ADDR_BITS 	13
#define GZ_LOWER_CHAR_ADDR_MSK 	0x0000fff8

#define GZ_SIZE					(1 << GZ_HIGHER_ADDR_BITS)

/*	Note that this GZ_MAP_SIZE is the count of unsigned integers in the map
 *	and not bytes
 */
#define GZ_MAP_SIZE 			(1 << GZ_LOWER_ADDR_BITS)
#define GZ_BITS_PER_INT			(1 << GZ_BIT_POSITION_BITS)
#define	GZ_BITS_PER_BYTE		(1 << GZ_NUMBER_OF_BITS)

#define GZ_GUARD_ZONE				GZ_TRUE
#define GZ_NON_GUARD_ZONE			GZ_FALSE

/*	Taking a cue from Linux kernel's usage of GCC's branch prediction method.	*/
#define	likely(x)				__builtin_expect((x), GZ_TRUE)
#define	unlikely(x)				__builtin_expect((x), GZ_FALSE)

/*  Note that this value here must the value defined in the modified glibc
 */
#define     MT_ARRAY_SIZE   79

//=============================================================================

typedef union {
	char bytes[4];
	float vl;
} custom_float;

static const custom_float guardzone_float = {.bytes = {23,0,0,0}};

// Extern variables for minimum and maximum zone size.
// These can be set by specifying command line options to cilly.
extern unsigned int min_zone_size;
extern unsigned int max_zone_size;

static const char zone_value = 23;

//=============================================================================

/*	This variable is basically used when attempting to find the performance of
 *	fast checks only by replacing the slow check component by an instruction
 *	incrementing this global variable.
 */
#ifdef GZ_FAST_CHECKS_ONLY
int slow_checks_counter;
#endif

/*	Thread specific variable used in memory-allocation routines to determine
 *	the size of the type whose pointer is being assigned the memory chunk
 *	returned the memory-allocation routine.	
 *	NOTE that this variable MUST NOT be initialized. 
 *	Hence each transformed file will have this declaration which will be
 *	considered by the compiler to be a "common" variable.
 *
 *	Note that this variable name MUST also be excluded from transformation.
 */
extern __thread unsigned type_size;

// Guard map: defined as extern because it is defined in glibc.
extern unsigned *guard_map[GZ_SIZE];

//=============================================================================

/*
 * Note that the function has been attributed as "pure" because:
 * 	1.	It has no side-effects (on both the parameters and the global
 * 		variables)
 * 	2.	It depends on global variable (guardmap)
 */
void is_guardzone() asm("asm_is_guardzone") __attribute__((pure));
 
void mark_guardzone (void *address, unsigned int count);
 
void unmark_guardzone (void *address, unsigned int count);

void alloc_guard_map_page (unsigned higher_index);

//=============================================================================

/*	The basic objective of this section is to specify all the functions as
 *	inline so that cilly does not automatically delete them	*/
/*
 * Note that these functions have been attributed as "pure" because:
 * 	1.	It has no side-effects (on both the parameters and the global
 * 		variables)
 * 	2.	It depends on global variable (guardmap)
*/

static unsigned is_array_acc_unsafe (unsigned int index, unsigned int array_size) 
		__attribute__((always_inline, const));

static void ensure_addr_guard_map (void *, void *) __attribute__((always_inline));

static void ensure_sframe_guard_map () __attribute__((always_inline));

//=======================================================================
//  Macros that Initialize and uninitialize guardzones of transformed
//  variables on stack and global area.
//=======================================================================

/*
 * The base macro that sets/unsets guard zones and
 * the guard map corresponding to them. 
 *
 * set_or_unset_gz is a boolean that determines if
 * we want to set or unset actual guard zone themselves.
 *
 * Currently, as a part of optimization, we do not unset
 * guard zones during uninitialization. We only unset guard map
 * corresponding to the guard zone during uninitialization.
 * set_or_unset_gz is set to 1 when we want to set
 * or unset guard zones as well as guard map. Otherwise,
 * it is set to 0.
 */
#define set_guardzones(obj, value, set_or_unset_gz) 						 			 \
do {																																	 \
																																			 \
	unsigned byte_count = ((unsigned) sizeof(obj)); 										 \
	unsigned address = (unsigned) (&obj);																 \
																																			 \
	if (((byte_count % 8) != 0) ||																       \
	   ((address % 8) != 0)) 																						 \
		abort(); 																													 \
																																			 \
	unsigned higher_index = 																						 \
		( address >> GZ_HIGHER_ADDR_BITS);																 \
	unsigned lower_index = 																							 \
	((address & GZ_LOWER_CHAR_ADDR_MSK) >> 															 \
	 	GZ_NUMBER_OF_BITS);																								 \
																																			 \
	if (set_or_unset_gz)																					 			 \
		if (value == 0xFF)																								 \
			memset((void*) address, zone_value, byte_count);								 \
		else																															 \
			memset((void*) address, 0, byte_count);													 \
																																			 \
	char * curr_addr = address; 																				 \
																																			 \
	while(byte_count > 0) { 																						 \
																																			 \
		char *next_page_boundary = 																				 \
		(char *)((higher_index + 1) << GZ_HIGHER_ADDR_BITS); 							 \
		unsigned int page_addr_remaining = (next_page_boundary - curr_addr); \
																																			 \
		unsigned int bits_to_set = (byte_count <= page_addr_remaining)? 	 \
									byte_count : page_addr_remaining; 									 \
																																			 \
		memset( (((char *)guard_map[higher_index]) + lower_index), 				 \
					value, (bits_to_set / 8)); 																	 \
																																			 \
		curr_addr = (char *)((++higher_index) << GZ_HIGHER_ADDR_BITS); 		 \
		lower_index = 0; 																									 \
		byte_count -= bits_to_set; 																				 \
	} 																																	 \
} while (0)

/*	
 *	A macro to initialize an area with guardzone values and also mark the
 *	guardmap.
 *	Note that this macro can only be used for stack variables where it
 *	is guaranteed apriori that map pages corresponding to the stack have
 *	been allocated.
 *	Note that we now have another invariant that the values of guardzones will
 *	be initialized in the structures themselves. Hence now we just have to set
 *	the guardmap.
 */
#define init_both_guardzones(obj) 																	\
do {																																\
	set_guardzones(obj.gz_front, 0xFF, 1);														\
	set_guardzones(obj.gz_rear, 0xFF, 1);															\
} while (0)																													\

/*	
 *	Note that during uninitialization it's not necessary to 
 *	remark the ptr area with anything. HOWEVER it is important 
 *	to uninitialize the guardmap. Note that this macro can only 
 *	be used for stack variables where it is guaranteed apriori 
 *	that guardmap pages corresponding to the stack have 
 *	been allocated. For performance reasons, we do not unmark
 *	guard zones themselves. This approach is followed on
 *	all stack guard zone uninitializations.
 */
#define uninit_both_guardzones(obj) 												\
do {																												\
	set_guardzones(obj.gz_front, 0, 0);												\
	set_guardzones(obj.gz_rear, 0, 0);												\
} while (0)

/*	
 *	A macro to initialize an AREA OF FRONT GUARDZONE ONLY 
 *	with guardzone values and also mark the
 *	guardmap.
 *
 *	It is used to initialize guardzone of 
 *	individual field in SuperStruct and incomplete
 *	structures.
 */
#define init_front_guardzone(obj) 												\
do {																											\
	set_guardzones(obj.gz_front, 0xFF, 1);									\
} while (0)										


/*	A macro to uninitialize an AREA OF FRONT GUARDZONE ONLY 
 *	and also unmark the guardmap.
 *	
 *	It is used to uninitialize guardzones of 
 *	individual field in SuperStruct and incomplete structures.
 */
#define uninit_front_guardzone(obj) 											\
do {																											\
	set_guardzones(obj.gz_front, 0, 0);											\
} while (0)										

/*	
 *	A macro to initialize an AREA OF REAR GUARDZONE ONLY 
 *	with guardzone values and also mark the guardmap.
 *
 *	It is used to initialize guardzone of last extra 
 *	field in SuperStruct.
 */
#define init_rear_guardzone(obj) 													\
do {																											\
	set_guardzones(obj.gz_rear, 0xFF, 1);										\
} while (0)										

/*	
 *	A macro to uninitialize an AREA OF REAR GUARDZONE ONLY 
 *	by marking the guardmap. For better performance, 
 *	we don't uninitialize the guardzone itself.
 *
 *	It is used to uninitialize guardzone of last extra 
 *	field in SuperStruct.
 */
#define uninit_rear_guardzone(obj) 													\
do {																												\
	set_guardzones(obj.gz_rear, 0, 0);												\
} while (0)									

/*
 * Macro to uninitialize guardzones of a superstruct.
 * As stated previously, we don't clear guardzones themselves.
 * We just uninitialize guardmap.
 */
#define uninit_superstruct_guardzones(obj) 								 \
do {																											 \
	set_guardzones(obj, 0, 0);													 		 \
} while (0)

/*	
 *	The macro below is the "partial" initialization of a variable 
 *	that has been defined AND initialized in the definition itself.
 *	Hence all that needs to be done is the setting of the guardmap, 
 *	hence the	term partial
 *	
 *	Note that there is no need to do any init checks 
 *	because we know this can be called by only the file 
 *	that has the variable definition.
 */
#define	partial_init(obj)																			 \
do { 																													 \
	obj##_init__ = 1;																						 \
	ensure_addr_guard_map(&(obj), 															 \
			(((char *)&(obj)) + sizeof(obj)));											 \
																															 \
	set_guardzones(obj.gz_front, 0xFF, 0);											 \
	set_guardzones(obj.gz_rear, 0xFF, 0);												 \
} while(0)

/*
 *	Note that the macro below holds for the case when 
 *	the variable has been defined in the given file BUT 
 *	not initialized. Thus even the setting of
 *	values in the guardzone must be done here.
 */
#define	complete_init(var_name)																 \
do {																													 \
    if (! var_name##_init__) { 																 \
														        													 \
        var_name##_init__ = 1;																 \
        ensure_addr_guard_map(&(var_name), 										 \
		        (((char *)&(var_name)) + sizeof(var_name)));			 \
        init_both_guardzones(var_name);												 \
    }																													 \
} while (0)																										 \

//=============================================================================

/*	
 *	The macro below is the "partial" initialization of a 
 *	variable that has been defined AND initialized in the 
 *	definition itself.
 *	
 *	Hence all that needs to be done is the setting of the 
 *	guardmap. Hence the	term partial
 *
 *	Note that there is no need to do any init checks because 
 *	we know this can be called by only the file that has 
 *	the variable definition.
 */
#define	front_partial_init(obj)																	\
do { 																														\
																																\
	obj##_init__ = 1;																							\
	obj##_ptr = &(obj.orig_var)																		\
	ensure_addr_guard_map(&(obj), 																\
			(((char *)&(obj)) + sizeof(obj)));												\
																																\
	set_guardzones(obj.gz_front, 0xFF, 0);											  \
} while(0)

/*
 *	Note that the macro below holds for the case when 
 *	the variable has been defined in the given file BUT 
 *	not initialized. Thus even the setting of
 *	values in the guardzone must be done here.
 */
#define	front_complete_init(obj)												\
do {																										\
    if (! obj##_init__) { 															\
																												\
		obj##_init__ = 1;																		\
		obj##_ptr = &(obj.orig_var)													\
		ensure_addr_guard_map(&(obj), 												\
				(((char *)&(obj)) + sizeof(obj)));							\
		init_front_guardzone(obj);													\
																												\
	}																											\
} while (0)																							\

/*	
 *	The objective of the following macro is to set values 
 *	in structures to the supplied value. This is done 
 *	through a pointer specifically because the
 *	particular field could be a const which could 
 *	never be assigned through legal means.
 */
#define	correct_struct_field(type_expr, target, value)	\
do {																										\
	typeof(type_expr) ptr = &target;											\
	*ptr = value;																					\
} while (0)																							\
								

//=============================================================================

/*	
 *	This is a simple macro that calls abort if argument is true. Note that we
 *	need to make this into a macro because we want to inline it AND we cannot
 *	use function because although it can be inlined, we cannot declare it to
 *	have attribute "pure" because its return type will be void.
 */
//	This macro basically disables calls to the extensive guardmap checking
#ifndef	GZ_FAST_CHECKS_ONLY
#define	gz_abort(arg)					if (unlikely(arg)) abort()
#else
/*	
 *	Note that here we NEED to do something else the compiler optimizes out the
 *	fast checks also. Thus we write an inline assembly instruction in the
 *	then-statement because the compiler does not analyse inline assembly and
 *	just uses it.
 */
#define	gz_abort(arg)					if (unlikely(arg)) ++slow_checks_counter
#endif


//=============================================================================

/*	
 *	The objective of the following section of code is to measure how many
 *	"misses" the fast guardzone check endures. That is how many calls go to the
 *	more extensive guardmap check.
 *
 *	Note that the definition of the function below is to be included ONLY in
 *	the main file.
 */

#ifdef	GZ_INSTR_MISS_RATE
#ifdef	GZ_MAIN_FILE

long double gz_total_checks;
long double gz_guardmap_checks;

void
gz_miss_rate(void)
{
	printf("\ngz_total_checks = %LG", gz_total_checks);
	printf("\ngz_guardmap_checks = %LG\n", gz_guardmap_checks);
}

/*	To "register" this function, we need an init function.
 *	*/
void
__attribute__((constructor)) gz_reg_miss_rate()
{
	atexit(&gz_miss_rate);
}

#else

extern long double gz_total_checks;
extern long double gz_guardmap_checks;

#endif	//	GZ_MAIN_FILE
#endif	//	GZ_INSTR_MISS_RATE

//=============================================================================
//  Macros to verify if a dereference is valid or invalid
//=============================================================================
/*	Note that what we want is basically to use the literals for representing 
 *	the guardzone bit sequences that we want to compare against.
 *	Hence the representation of literals is EXTREMELY important. They must
 *	indicate the correct size that we want the compiler to use or else compiler
 *	takes to them to be 32-bit or something and does comparisons directly with
 *	the memory.
 *	
 *	Since in case of character data, compiler uses movzbl to bring the char
 *	bytes into a 32-bit register after sign extending them, we will use the
 *	literal 0x00000017 for comparison.
 *	What needs to be checked is whether this works ONLY for unsigned character
 *	or this works for signed character as well.
 */

/*	
 *	The basic objective in the inline assembly used in is_char_guard is not to
 *	let gcc know that a function call is being made and to make sure that the
 *	particular block of code never messes any of the registers eax, ecx and
 *	edx even after the function call.
 */	
#ifndef	GZ_FAST_CHECKS_ONLY
#define	is_char_guard(origValue, value, ptr)		{				 \
																												 \
	unsigned gz_value_size = (sizeof(origValue) < 				 \
													sizeof(value)) ? 							 \
					sizeof(origValue) : sizeof(value);						 \
																												 \
	if (gz_value_size == 1)																 \
		gz_abort_arg = (																		 \
				(value) == '\x17'); 														 \
	else if (gz_value_size == 2)													 \
		gz_abort_arg = (																		 \
				(value) == L'\x17\x17'); 												 \
	else if (gz_value_size == 4)													 \
		gz_abort_arg = (																		 \
				(value) == 0x17171717); 												 \
	else 																									 \
		gz_abort_arg = (*((int *)(ptr)) == 0x17171717);			 \
																												 \
	{																											 \
		if (unlikely(gz_abort_arg))	{												 \
			{ 																								 \
					unsigned ptrval = ptr;												 \
					asm (																					 \
					"pushl %0 \n"																	 \
					"pushl %%ecx \n"															 \
				 	"pushl %%edx \n"															 \
					"pushl %%eax \n"															 \
					"pushl %%eax \n"															 \
					"mov 0x10(%%esp), %%eax \n"						 			 	 \
					"mov %%eax, (%%esp) \n"												 \
					"call asm_is_guardzone\n"										 	 \
					"popl %%eax \n"																 \
					"popl %%eax \n"																 \
					"popl %%edx \n"															 	 \
				 	"popl %%ecx \n"																 \
					"popl %0 \n"																	 \
					: 																						 \
					: "m" (ptrval)														 		 \
					: "cc"																				 \
				);																							 \
				gz_abort_arg;																	 	 \
			}																									 \
		}																										 \
	}																									 		 \
  /* 																										 \
	{																											 \
		if (unlikely(gz_abort_arg)) {												 \
			{																									 \
					is_guardzone(ptr);													 	 \
					gz_abort_arg;																 	 \
			}																									 \
		}																										 \
	}*/																									   \
}																												 \

#else	
#define	is_char_guard(value, ptr)		{										\
	if (sizeof((value)) == 1)															\
		gz_abort_arg = (																		\
				(value) == 0x00000017); 												\
	else if (sizeof((value)) == 2)												\
		gz_abort_arg = (																		\
				(value) == 0x00001717); 												\
	else if (sizeof((value)) == 4)												\
		gz_abort_arg = (																		\
				(value) == 0x17171717); 												\
	else 																									\
		gz_abort_arg = (*((int *)(ptr)) == 0x00000017);			\
																												\
	if (unlikely(gz_abort_arg))														\
		asm volatile ("" : : "m" (*(ptr)));									\
}
#endif	/* GZ_FAST_CHECKS_ONLY */

/*
 * Check if the float value is guard zone value.
 */
#define	is_float_guard(value, ptr)	{										\
	if (sizeof((value)) == 4) 														\
		gz_abort_arg = (																		\
		((value)) == guardzone_float.vl); 									\
	else																									\
		gz_abort_arg = (																		\
		(	*( (float *)(ptr) )) == guardzone_float.vl); 			\
																												\
	if (unlikely(gz_abort_arg))	 {												\
		asm (																								\
				"pushl %%eax \n"																\
				"pushl %%ecx \n"																\
			 	"pushl %%edx \n"																\
				"lea %0, %%eax\n"																\
				"pushl %%eax \n"																\
				"call asm_is_guardzone\n"												\
				"popl %%eax\n"																	\
				"popl %%edx \n"																	\
			 	"popl %%ecx \n"																	\
				"popl %%eax \n"																	\
				: 																							\
				: "m" (*(ptr))																	\
				:	"cc"																					\
			);																								\
	}																											\
}

/*	The basic objective of this method is to check whether an array access is
 *	safe. It just compares the index used with size of the array.	
 *	It's just being made into a function so that it can be used by CIL
 *	transformer.
 *
 *	Note that this is NOT supposed to be used with either:
 *	1.	Arrays within structs	
 *	2.	Arrays with length not specified	
 */
static unsigned
is_array_acc_unsafe(unsigned int index, unsigned int array_size)
{
	if (index > array_size)
		return GZ_TRUE;

	return GZ_FALSE;
}

//==============================================================
// Functions that setup guardmap for stack activation record
//==============================================================
static void
ensure_addr_guard_map(void *addr_start, void *addr_end)
{
		unsigned curr_higher_index, final_higher_index;

		curr_higher_index = ((unsigned)addr_start) >> GZ_HIGHER_ADDR_BITS;
		final_higher_index = ((unsigned)addr_end) >> GZ_HIGHER_ADDR_BITS;

		do {
			if (likely((unsigned) guard_map[curr_higher_index]))
				continue;
			else
				alloc_guard_map_page(curr_higher_index);
			
		}
		while(unlikely(++curr_higher_index <= final_higher_index));
}

/*
 * This function is called at the start of each function call. The basic
 * objective of this function is to ensure that the guardmap pages
 * corresponding to the entire current stack frame are present in our guardmap.
 * The flag formal parameter specifies whether the current function has any
 * transformed variable. The point being that if the current function does
 * not have any transformed local variables then we should not be be
 * executing the function.
 */
static void
ensure_sframe_guard_map()
{
		void * frame_start, *frame_end;

		//	Here we are marking the start and end of the frame.
		//	Note that in x86 the stack grows down. Hence %esp < %ebp
		asm volatile ("mov %%esp, %0" : "=g" (frame_start):);
		asm volatile ("mov %%ebp, %0" : "=g" (frame_end):);
		
		ensure_addr_guard_map(frame_start, frame_end);
}
//=============================================================================
#endif
