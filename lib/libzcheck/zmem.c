#include	<zcheck.h>

#define	_GNU_SOURCE
#include	<dlfcn.h>

/*	Note that from inside zmem's malloc, we need to use dynamic library
 *	method to locate the default memory allocation units	*/
static void *(*libc_malloc)(size_t);
static void *(*libc_calloc)(size_t, size_t);
static void (*libc_free)(void *);

/*	Forward declaration.	*/
int
get_redzone(char *addr, redzones *addr_rz);

void __attribute__((constructor))
zmem_init(void) 
{
	libc_malloc = dlsym(RTLD_NEXT, "malloc");
	libc_calloc = dlsym(RTLD_NEXT, "calloc");
	libc_free  = dlsym(RTLD_NEXT, "free");
}

/*	The objective of this function is to do post-processing of the memory
 *	received from the library memory functions.
 *	This includes setting up the redzones, computing the ptr to be returned
 *	and setting value of the rear-zone-ptr.
 *	Note that size argument here refers to the original size and NOT the new
 *	size	*/
void *
alloc_post_processing(void *ptr, size_t size)
{
	char *rear_rz_ptr, *front_rz_ptr;

	/*	Setting up the front redzone	*/
	front_rz_ptr = (char *)ptr + sizeof(char **);
	memset(front_rz_ptr, zone_value, zone_size); 
	mark_redzone(front_rz_ptr, zone_size);

	/*	Setting up the intermediate area. Note that the intermediate area must
	 *	be present and marked as non-redzone	 
	 */
	unmark_redzone(front_rz_ptr + zone_size, size);
	
	/*	Setting up the rear redzone	*/
	rear_rz_ptr = front_rz_ptr + zone_size + size; 
	memset(rear_rz_ptr, zone_value, zone_size); 
	mark_redzone(rear_rz_ptr, zone_size);

	/*	Setting up the pointer to the rear redzone	*/
	*(char **)ptr = rear_rz_ptr;

	/*	Return the pointer to the buffer	*/
	return (front_rz_ptr + zone_size);
	
}

/*	This function is used to dynamically allocate memory. It also writes
 *	meta-data into the memory for keep track of the end redzone. This is
 *	helpful when the memory is de-allocated	*/

/*	The layout of the memory is as follows:
 *	--------------------------------------------------------------------
 *		| Rear_rz_ptr | Front-red-zone | Memory | Rear-red-zone|	 
 *	-------------------------------------------------------------------
 *	*/
void*
malloc(size_t size)
{
	void *ptr;
	size_t new_size = size + 2*zone_size + sizeof(char **);

	if((ptr = libc_malloc(new_size)) == 0) 
		return 0;
	
#ifdef	ZDEBUG	
	redzones redzone;
	void *addr = alloc_post_processing(ptr, size);

	if (get_redzone(addr, &redzone))
		printf("malloc : %p\nerror in allocating redzones.\n", addr);

	return addr;
#else
	return alloc_post_processing(ptr, size);
#endif
}

/*	Replicating the functionality of z_malloc as above.	*/
void*
calloc(size_t nmemb, size_t size)
{
	void *ptr;
	/*	Calculating new number of elements so that the redzones can be
	 *	accomodated in their place	*/
	size_t add_size = (2*zone_size + sizeof(char **));
	size_t new_num = nmemb + add_size/size + ((add_size%size)?1:0);

	if((ptr = libc_calloc(new_num, size)) == 0) {
#ifdef	ZDEBUG
		printf("calloc: error in libc call.\n");
#endif
		return 0;
	}

#ifdef	ZDEBUG	
	redzones redzone;
	void *addr =  alloc_post_processing(ptr, (nmemb*size));

	if (get_redzone(addr, &redzone)) 
		printf("calloc : %p\nerror in allocating redzones.\n", addr);
	
	return addr;
#else
	return alloc_post_processing(ptr, (nmemb*size));
#endif
}


/*	The basic idea in z_realloc is to just to malloc a new area of the
 *	relevant size, copy the old  */
void*
realloc(void *ptr, size_t size)
{
	void *realloc_ptr, *realloc_buffer;

	size_t new_size = size + 2*zone_size + sizeof(char *);
	size_t orig_size;

	/*	This is the size argument that we will provide to memset to copy
	 *	user-data from original buffer to newly allocated buffer	*/
	size_t memset_size;

	redzones rz_addr;
	
	/*	From the ptr supplied as parameter, compute the addresses of the front
	 *	redzone and the rear redzone.
	 *	We need this because we need to calculate the size of current buffer
	 *	when doing the reallocation	*/

#ifdef	ZDEBUG
	printf("realloc :\naddress : %p\tsize : %d\n",ptr, size);
#endif

	/*	If this value is null, it implies that there was either some corruption of
	 *	metadata	*/
	if(get_redzone(ptr, &rz_addr))
		abort();

	/*	If the size=0 is passed to realloc it returns either null or a pointer
	 *	suitable to be passed to free()	*/
	if(!size)
		return 0;

	/*	We can behave as if realloc failed and return the original pointer.	*/
	if((realloc_ptr = libc_malloc(new_size)) == 0)
		return ptr;

	/*	Setting up the redzones for the new area allocated to us. The pointer
	 *	returned to us points to the buffer to be returned to the caller	*/
	realloc_buffer = alloc_post_processing(realloc_ptr, size);

	/*	The original size of the buffer in bytes	*/
	orig_size = rz_addr.rz_front - rz_addr.rz_rear;

	/*	Note that the size provided to memset is to be the minimum of the two
	 *	sizes: original buffer size and the buffer size requested	*/
	memset_size = (orig_size > size) ? size : orig_size;
	
	/*	Copy the contents of the original buffer to the new buffer	*/
	memcpy(realloc_buffer, rz_addr.buffer, memset_size);
	
	/*	Unmark redzones in our original buffer	*/
	unmark_redzone(rz_addr.rz_front, zone_size);
	unmark_redzone(rz_addr.rz_rear, zone_size);

	/*	Free up the original buffer. Note that this field is the beginning of
	 *	our meta-data */
	libc_free(rz_addr.rz_rear_ptr);

	return realloc_buffer;
}

void
free(void *ptr)
{
	redzones addr_rz;

	/*	From the ptr supplied as parameter, compute the addresses of the front
	 *	redzone and the rear redzone	*/
	/*	If this value is null, it implies that there was either some corruption of
	 *	metadata OR we did not allocate this memory.	*/
	if(get_redzone(ptr, &addr_rz)) {
#ifdef ZDEBUG
		printf("free : ptr : %p\naborting free.\n", ptr );
		return;
#else
		abort();
#endif
	}
	/*	Pass the pointer to the start of the buffer	*/
	libc_free(addr_rz.rz_rear_ptr);

	/*	Reset the redzones in our bitmap	*/
	unmark_redzone(addr_rz.rz_front, zone_size);
	unmark_redzone(addr_rz.rz_rear, zone_size);

	return;
}	

/*	This function is used by z_free function. The basic objective is to find
 *	the start and end redzones for dynamically allocted memory. This uses the
 *	metadata written into the dynamically allocated memory when the allocation
 *	is done.	
 *	*/

/*	The layout of the memory is as follows:
 *	---------------------------------------------------------------------
 *	| rz_rear_ptr 		| rz_front 			|   buffer 	| rz_rear		|	 
 *	| Rear-redzone-ptr 	| Front-red-zone 	|  			| Rear-red-zone	|	 
 *	---------------------------------------------------------------------
 *	
 *
 *	NOTE THAT THE CALLER WOULD HAVE TO DO A LOT OF ERROR CHECING AS FOLLOWS:
 *	*/

/*	The best case scenario is:
 *	1.	The address provided to us is not in redzone.
 *	2.	The front and rear pointers point to a redzone.
 *
 *	The above scenario indicates in high probability that the redzone is
 *	been correctly formatted.
 *
 *	1.	First, check to see if the address provided to us is not in a redzone. 
 *	If it is, then it is a clear case of error.
 *
 *	2.	Second check is to see if the area pointed to by first redzone is
 *	recognized by bitmap as a redzone. If it is, then we are looking at
 *	something that has been allocated by rz_malloc AND MAY BE at the
 *	beginning of the memory region.
 *		The "MAY BE" part is because we could have been given a pointer to
 *		middle of buffer allocated by rz_malloc but still could  locate the
 *		front redzone.
 *
 *	3.	The Third check is that pointer to rear_redzone is again recognized by the
 *	bitmap. If it is, then it means in high probability that we are on the
 *	right track.
 *		Note that, the rear_redzone is computed using the meta-data. There is
 *		a low probability that even in case of a pointer provided to us
 *		pointing in the middle of a redzone, and the computed rear_redzone is
 *		pointing to some-other area's redzone. Low probability BUT can happen.
 *
 * 		If it fails, then we were definitely given an area in the middle of a
 * 		valid buffer. AND that would have screwed up free().
 *
 *	4.	If all the checks are cleared, then in good probability we are looking at a
 *	memory area that has been allocated by us.
 *	
*/

/*	This function will return a non-zero value in case of an error. Else zero
 *	is returned.	*/
int
get_redzone(char *addr, redzones *addr_rz) 
{
	addr_rz->buffer = addr;
	addr_rz->rz_front = addr - zone_size;
	addr_rz->rz_rear_ptr = (char **)(addr_rz->rz_front - sizeof(char **));
	addr_rz->rz_rear =  *(addr_rz->rz_rear_ptr);

	/*	Lets perform the error checks as specified out	 */
	if (!(is_redzone(addr)) && is_redzone(addr_rz->rz_front) && 
			is_redzone(addr_rz->rz_rear)) {
		return 0;
	}

#ifdef	ZDEBUG
		printf("get_redzone error for ptr : %p\n", addr);
#endif
	return -1;

}
