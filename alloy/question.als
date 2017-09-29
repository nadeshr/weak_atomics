open c11[E] as M1             // the C11 memory model
open util/ordering[E] as ord  // library for building orders

sig E {}

// well-formed schedule
pred wf_schedule [X : Exec_C] {

  // Construct co by projecting all the writes to the same atomic location
  // from the execution order.
  all e1, e2 : E |
    (e1 -> e2) in X.co iff (
      (e1 -> e2) in (X.(W - naL) <: X.sloc :> X.(W - naL)) and 
      ord/lt[e1,e2]
    )
  
  // Construct rf by relating each read of location x to the most recent 
  // write to x in the execution order. If a given read of x has no
  // preceding writes to x, then the read will have no rf edge, which 
  // signifies that it is observing x's initial value.
  all e1, e2 : E |
    (e1 -> e2) in X.rf iff (
      (e1 -> e2) in (X.W <: X.sloc :> X.R) and 
      ord/lt[e1,e2] and 
      (all e1' : E | 
        (e1' -> e2) in (X.W <: X.sloc :> X.R) and 
        ord/lt[e1',e2] implies ord/lte[e1',e1])
    ) 

}

// constraints already imposed by LegUp scheduler
pred allowed_schedule_orig [X : Exec_C] {

  // preserve all RAW, WAR, and WAW dependencies within a loop iteration
  all e1, e2 : E | 
  (e1 -> e2) in X.(sb & sloc & site) - (X.R -> X.R) 
  => ord/lte[e1,e2]

  // preserve WAR dependencies from one iteration to the next
  all e1, e2 : E | 
  (e1 -> e2) in X.(sb & sloc & nite) & (X.W -> X.R) 
  => ord/lte[e1,e2]

  // preserve control, address, and data dependencies
  all e1, e2 : E |
  (e1 -> e2) in X.(cd + ad + dd)
  => ord/lte[e1,e2]  

}

pred allowed_schedule [X : Exec_C] {

  allowed_schedule_orig[X]

  // preserve all RAW, WAR, and WAW dependencies from one iteration to the next
  all e1, e2 : E | 
  (e1 -> e2) in X.(sb & sloc & nite) - (X.R -> X.R) 
  => ord/lte[e1,e2]

  // preserve the order between atomics on the same location
  all e1, e2 : E | 
  e1 in X.A and e2 in X.A and
  (e1 -> e2) in X.(sb & sloc) 
  => ord/lte[e1,e2]

  // NB: The following rules could be tweaked to allow reverse-roach-motel 
  // optimisation as well.

  // acquire reads and SC reads/writes
  // cannot be switched with later reads/writes
  all e1, e2 : E | (
    e1 in X.((acq + sc) & (R + W)) and
    e2 in X.(R + W) and (e1 -> e2) in X.sb   
  ) => ord/lte[e1,e2]

  // release writes and SC reads/writes 
  // cannot be switched with earlier reads/writes
  all e1, e2 : E | (
    e2 in X.((rel + sc) & (R + W)) and
    e1 in X.(R+W) and (e1 -> e2) in X.sb       // (try changing R+W to W)
  ) => ord/lte[e1,e2]

  // a read cannot be switched with a later read/write if they are
  // separated by an acquire fence
  all e1, e2, e3 : E | (
    e2 in X.(acq & F) and
    e1 in X.R and (e1 -> e2) in X.sb and
    e3 in X.(R + W) and (e2 -> e3) in X.sb
  ) => ord/lte[e1,e3] 

  // a write cannot be switched with an earlier read/write if they are
  // separated by a release fence
  all e1, e2, e3 : E | (
    e2 in X.(rel & F) and
    e3 in X.W and (e2 -> e3) in X.sb and
    e1 in X.(R + W) and (e1 -> e2) in X.sb
  ) => ord/lte[e1,e3] 

  // a read/write cannot be switched with an earlier read/write if they are
  // separated by an SC fence
  all e1, e2, e3 : E | (
    e2 in X.(sc & F) and
    e1 in X.(R + W) and (e1 -> e2) in X.sb and
    e3 in X.(R + W) and (e2 -> e3) in X.sb
  ) => ord/lte[e1,e3]  
}

pred is_inconsistent[X:Exec_C] {
  // We do not consider RMWs yet
  no_RMWs[X]

  // Assume sb is total within each thread
  total_sb[X]

  // Execution is dead (so its litmus test is not racy)
  M1/dead[X]

  // The execution is forbidden in C11
  not(M1/consistent[X])
}

pred find_bug [X : Exec_C] {

  // Execution is forbidden in software...
  is_inconsistent[X]

  // ... but is nonetheless allowed by a well-formed schedule.
  wf_schedule[X]
  allowed_schedule[X] // new constraints

}

// Configuration options
//-------------------------------
// Solver = Glucose
// Maximum stack = 65536k
// Maximum memory = 4096MB
// Use higher-order solver = YES
                                              // Solve time (EE-Benjamin)
//--------------------------------------------//-------------------------
run find_bug for exactly 1 Exec, 2 E expect 0 // <1 second
run find_bug for exactly 1 Exec, 3 E expect 0 // <1 second
run find_bug for exactly 1 Exec, 4 E expect 0 // <1 second
run find_bug for exactly 1 Exec, 5 E expect 0 // 3 seconds
run find_bug for exactly 1 Exec, 6 E expect 0 // 96 seconds 
run find_bug for exactly 1 Exec, 7 E expect 0 // 29 minutes
run find_bug for exactly 1 Exec, 8 E expect 0 // 9 hours
run find_bug for exactly 1 Exec, 9 E          // unknown (out of time)

// NB:
// 4 events are enough to find MP/LB/SB bugs that involve no fences
// 5 events are needed to find MP/LB/SB bugs that involve one fence
// 6 events are enough to find IRIW bugs that involve no fences

pred find_bug_seq [X : Exec_C] {

  // Assume every event is in the same thread
  sq[X.ev] in X.sthd

  // Execution is forbidden in software...
  is_inconsistent[X]

  // ... but is nonetheless allowed by a well-formed schedule.
  wf_schedule[X]
  allowed_schedule_orig[X] // original LegUp constraints

}

run find_bug_seq for exactly 1 Exec, 4 E expect 0
run find_bug_seq for exactly 1 Exec, 5 E expect 0 
run find_bug_seq for exactly 1 Exec, 6 E expect 0 
run find_bug_seq for exactly 1 Exec, 7 E expect 0 
run find_bug_seq for exactly 1 Exec, 8 E expect 0 
run find_bug_seq for exactly 1 Exec, 9 E expect 0  


