#define NUM_ACCEL 2 

#include <stdio.h>
#include <pthread.h>

volatile int y;
volatile int x;

void *writer (void * arg) {
	int value = *((int *) arg);

	// 3 divide 3 
	x = value/3;
	// Write flag
	y = 1;
	pthread_exit(0);

}

void *reader (void * arg) {
	int value = *((int *) arg);

	int r0 = 0;

	// Read flag
	int r1 = y;

	// If flag is set, read data
	if(r1==1) r0=x;

	printf("Message passing is broken!\n");
	printf("Flag (y) is %d, but data (x) is %d\n", r1, r0);   
	pthread_exit(0);
}


int main () {
	int i;
	//create the thread variables
	pthread_t my_threads[NUM_ACCEL];

	// passing in values to threads
	int arg0 = 3;   
	int arg1 = 1;   

	x = 0;

	//launch threads
	pthread_create(&my_threads[0], NULL, writer, (void *) &arg0);
	pthread_create(&my_threads[1], NULL, reader, (void *) &arg1);

	//join the threads
	for (i=0; i<NUM_ACCEL; i++) {
		pthread_join(my_threads[i], NULL);
	}

	return 0;
}
