#define NUM_ACCEL 2 

#include <stdio.h>
#include <pthread.h>

volatile int y;
volatile int x;

void *writer (void * arg) {
	int value = *((int *) arg);
	x = 1;
	pthread_exit(0);

}

void *reader (void * arg) {

	// insert these writes to avoid LegUp bug
	x = 0;
	y = 0;
	int value = *((int *) arg);

	// false delay
	int r0 = y + y + y + y + y + y;
	int r1 = x;
	
   // this load is scheduled as the first load from x
	int r2 = x / value;

	printf("r1 %d r2 %d\n",r1,r2);  
   printf("The load that was to provide an input to the divide was reordered\n"); 
   printf("and executed before the write to x in the previous thread.\n"); 
	pthread_exit(0);
}


int main () {
	int i;
	//create the thread variables
	pthread_t my_threads[NUM_ACCEL];

	int arg0 = 1;   
	int arg1 = 1;   

	x = 0;

	//launch threads
	pthread_create(&my_threads[0], NULL, reader, (void *) &arg1);
	pthread_create(&my_threads[1], NULL, writer, (void *) &arg0);

	//join the threads
	for (i=0; i<NUM_ACCEL; i++) {
		pthread_join(my_threads[i], NULL);
	}

	return 0;
}
