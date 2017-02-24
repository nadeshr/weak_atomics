This webpage contains additional material for [Hardware Synthesis of Weakly Consistent C Concurrency](https://nadeshr.github.io/papers/Nadesh_FPGA17.pdf). 

Contents
========
- Verifying that our scheduling constraints implement the C11 standard
- Verifying the lock-free circular buffer
- Motivating examples
- Experimental Data

1. Verifying that our scheduling constraints implement the C11 standard
---------
As explained in Section 4.4, we have used the Alloy tool to verify that our scheduling constraints are sufficient to implement the memory consistency model defined by the C11 standard. In the alloy folder, we provide the Alloy model files that we used. The first four are taken from Wickerson et al.'s work on comparing memory consistency models; the fifth is new.

- relations.als contains helper functions.
- exec.als encodes general program executions.
- exec_C.als encodes C11 program executions.
- c11.als encodes the constraints imposed by the C11 memory consistency model.
- question.als encodes our scheduling constraints, and several queries for checking that these scheduling constraints are strong enough to enforce the constraints required by the C11 memory consistency model.

To reproduce our result, save the five files above into the same directory, download Alloy, open question.als in Alloy, and run the queries contained within.

2. Verifying the lock-free circular buffer
----------------
As explained in Section 5.1, we have used the CppMem tool to verify that our case-study application, a lock-free circular buffer, is free from data races. In order to make the verification feasible, we removed the while-loop, replaced the array variable with a scalar, removed some unimportant local variables, and simplified the increment function. Below, we give the actual code that we verified.

	int main() {
	  atomic_int tail = 0;
	  atomic_int head = 0;
	  int arr = 0;
	  {{{ {
	    int chead = head.load(memory_order_acquire);
	    int ctail = tail.load(memory_order_relaxed);
	    if (ctail+1 != chead) {
	      arr = 42;
	      tail.store(ctail+1, memory_order_release);
	    }
	  } ||| {
	    int ctail = tail.load(memory_order_acquire);
	    int chead = head.load(memory_order_relaxed);
	    if (ctail != chead) {
	      arr;
	      head.store(chead+1, memory_order_release);
	    }
	  } }}}
	  return 0;
	}

To reproduce our result, paste the code above into CppMem's web interface and click Run. The tool should report (after a couple of minutes) that the code has 92 candidate executions, of which two are consistent, neither of which exhibit data races.

3. Motivating Examples
----------------------
We provide the actual code that displays coherence and message-passing violation in the motivating-examples folder, as described in Section 2 of our paper. These examples have been tested and verified on LegUp's VM. For convenience, we have included the output logs of each experiment for viewing. We include a "transcript" of the execution and a schedule trace, which can be visualised using LegUp's scheduleviewer.

4. Experimental Data
----------------------

We also provide the raw experiment data from Section 5 of our paper. We conduct two experiments, for which we provided raw data on all seven design points.

- results/chaining.csv contains the raw data for the chaining experiment.
- results/bursting.csv contains the raw data for the bursting experiment.
The version number are from 1 to 7 for Unsound, SC, OMP criticals, SC atomics, Weak atomics, Mutexes and OMP atomics respectively.


Contact
------------------
Please contact us at n_dot_ramanathan14_at_imperial_dot_ac_dot_uk for any problems/bugs. 

