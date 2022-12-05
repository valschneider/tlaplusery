----- MODULE migrate -----

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

CONSTANTS
	NULL,
	CPUS,
	MD_TASK, STOPPER_TASK, HPRIO_TASK, IDLE_TASK, TICK_TASK,
	AFFINER_TASKS

(* Per-CPU stopper task *)
STOPPER_TASKS == {STOPPER_TASK} \X CPUS
(* Task with prio > MD_TASK; one per CPU for sake of simplicity *)
HPRIO_TASKS   == {HPRIO_TASK}   \X CPUS
(* Per-CPU idle task *)
IDLE_TASKS    == {IDLE_TASK}    \X CPUS
TICK_TASKS    == {TICK_TASK}    \X CPUS

(*
 * Tasks influenced by schedule()
 *
 * Note that tasks setting the affinity are excluded; we assume there will
 * always be a CPU for them. Step interleaving will emulate preemption.
 *)
PCPU_TASKS  == STOPPER_TASKS \union HPRIO_TASKS \union IDLE_TASKS
SCHED_TASKS == {MD_TASK} \union PCPU_TASKS
TASKS       == SCHED_TASKS \union AFFINER_TASKS \union TICK_TASKS

(* Per-CPU static helpers *)
PCPU_TASK(tsk, cpu) == <<tsk, cpu>>
PCPU_TASK_CPU(tsk)  == tsk[2]

(* The result of CHOOSE is deterministic for a given input *)
INIT_CPU == CHOOSE cpu \in CPUS : TRUE

(* --algorithm main {
variables
	task_structs = [tsk \in TASKS |->
		   (* Note: non-reentrant migrate_disable()  *)
		   [migration_disabled |-> FALSE,
		   cpus_mask           |->
			IF tsk \in PCPU_TASKS THEN {PCPU_TASK_CPU(tsk)}
			ELSE                     CPUS,
		   pending_ref         |-> NULL,
		   prio                |->
			IF      tsk \in STOPPER_TASKS THEN 3
			ELSE IF tsk \in HPRIO_TASKS   THEN 2
			ELSE IF tsk = MD_TASK       THEN 1
			ELSE                             0]
	];

	preempt_count = [tsk \in TASKS |-> 0];

	(* MD_TASK starts on CPU1. All other tasks are per-CPU. *)
	task_cpu  = [tsk \in SCHED_TASKS |->
			IF tsk \in PCPU_TASKS THEN PCPU_TASK_CPU(tsk)
			ELSE                     INIT_CPU
		    ];
	runqueues = [cpu \in CPUS |->
			{PCPU_TASK(IDLE_TASK, cpu)} \union
			IF cpu = INIT_CPU THEN {MD_TASK} ELSE {}
		    ];
	currents  = [cpu \in CPUS |->
			IF cpu = INIT_CPU THEN MD_TASK
			ELSE            PCPU_TASK(IDLE_TASK, cpu)
		    ];

	(*
	 * Emulate affine_move_task()'s stack variables. One per task simplifies
	 * things; assumes non-reentrancy, see NonReentrantSCA.
	 *)
	my_pending   = [tsk \in TASKS |-> MY_PENDING_INIT];
	stopper_wait = [tsk \in TASKS |-> FALSE];

	pi_locks = [tsk \in TASKS |-> NULL];

	(* stopper->works list *)
	stopper_work = [ cpu \in CPUS |-> << >> ];

define {
	(* Helpers *)
	task_on_rq_queued(p) == \E cpu \in CPUS : p \in runqueues[cpu]
	task_running(cpu, p) == currents[cpu] = p

	is_migration_disabled(p) == task_structs[p].migration_disabled

	stopper_has_work(cpu) == Len(stopper_work[cpu]) > 0

	(* Type definitions  *)

	MY_PENDING_INIT    == [completed |-> FALSE, refcount |-> 0]
	MIGRATION_ARG_INIT ==  [
		p        |-> NULL,
		pending  |-> NULL,
		dest_cpu |-> NULL,
		done     |-> FALSE
	]

	TaskStructType == task_structs \in [TASKS ->
		[migration_disabled : BOOLEAN,
		 cpus_mask          : (SUBSET CPUS) \ {},
		 pending_ref        : TASKS \union {NULL},
		 prio               : Nat]
	]

	TypesOK ==
		/\ \A tsk \in SCHED_TASKS : task_cpu[tsk] \in CPUS

		/\ preempt_count \in [TASKS -> Nat]

		/\ \A cpu \in CPUS :
		  /\ \A id \in DOMAIN stopper_work[cpu] : stopper_work[cpu][id] \in
			[p        : TASKS \union {NULL},
			 pending  : TASKS \union {NULL},
			 dest_cpu : CPUS \union {NULL},
			 wait     : TASKS \union {NULL}]
		  /\ runqueues[cpu] \subseteq SCHED_TASKS
		  /\ currents[cpu] \in SCHED_TASKS

		/\ my_pending \in [TASKS -> [completed : BOOLEAN, refcount : Nat]]
		/\ pi_locks \in [TASKS -> TASKS \union {NULL}]

	(* Process enablement control via scheduler *)
	ProcessEnabled(self) ==
		IF self \notin SCHED_TASKS THEN TRUE
		ELSE \E cpu \in CPUS : currents[cpu] = self

	(* Invariants *)

	RefcountOK == \A task \in TASKS: my_pending[task].refcount >= 0

	(* Task on a CPU & !pending_ref => affinity mask respected *)
	AffinityOK ==
		\A cpu \in CPUS :
		  (MD_TASK = currents[cpu] /\ task_structs[MD_TASK].pending_ref = NULL) =>
		    \/ cpu \in task_structs[MD_TASK].cpus_mask
		    (*
		     * Ugly ahead: this should be a liveness condion where
		     * *eventually* (~>) the CPU is fixed up to match affinity.
		     *
		     * Since checking liveness takes ages and prevents using
		     * symmetry optimisations, we restrain that to:
		     * if the lock is free, then either affinity is respected
		     * or a pending was installed to move it away.
		     *)
		    \/ pi_locks[MD_TASK] \in TASKS

	QueuesOK ==
		\A a, b \in CPUS:
		  /\ currents[a] \in runqueues[a]
		  /\ a # b =>
		    (* A single task runs on a single CPU *)
		    /\ currents[a] # currents[b]
		    (* Enqueued sets are disjoint for any two runqueues *)
		    /\ runqueues[a] \cap runqueues[b] = {}

	NonReentrantSCA(self) ==
		\E id \in DOMAIN stack[self] : stack[self][id].procedure = "set_cpus_allowed_ptr" =>
		    \A other \in DOMAIN stack[self] \ {id} :
		      stack[self][other].procedure # "set_cpus_allowed_ptr"

	(* For symmetry optimisations *)
	Perms == Permutations(CPUS) \union Permutations(AFFINER_TASKS)
}

(* Scheduling *)

macro __schedule(cpu)
{
	(* XXX no one holds it pi_lock *)
	(* Set highest prio runnable task as current *)
	with (tsk \in {t \in runqueues[cpu] : \A other \in runqueues[cpu] \ {t} :
	      task_structs[t].prio >= task_structs[other].prio})
		currents[cpu] := tsk;
}

macro schedule()
{
	__schedule(CHOOSE cpu \in CPUS : currents[cpu] = self)
}

macro schedule_preempt()
{
	if (self \in SCHED_TASKS /\ preempt_count[self] = 0)
		schedule();
}

macro wake(p)
{
	(* XXX: if MD_TASK can sleep, this needs to use "cpus_ptr" *)
	assert ~task_structs[p].migration_disabled;

	(*
	 * Note this doesn't grab any locks, so a task can be enqueued
	 * despite another holding task_rq_lock.
	 *)
	with (cpu \in task_structs[p].cpus_mask) {
		task_cpu[p]    := cpu;
		runqueues[cpu] := runqueues[cpu] \union {p};
	}
}


macro stop_one_cpu_nowait(cpu, work)
{
	stopper_work[cpu] := Append(stopper_work[cpu], work);
	wake(PCPU_TASK(STOPPER_TASK, cpu));
}

macro sleep()
{
	runqueues[task_cpu[self]] := runqueues[task_cpu[self]] \ {self};
	schedule();
}

macro preempt_disable()
{
	preempt_count[self] := preempt_count[self] + 1;
}

macro preempt_enable()
{
	preempt_count[self] := preempt_count[self] - 1;
	schedule_preempt();
}

(* Locking *)

(*
 * Doesn't reuse above rq_lock macros to employ a single multiple assignement
 * statement (this saves us a few labels down the line).
 *)
macro task_rq_lock(p)
{
	await pi_locks[p] = NULL;
	pi_locks[p] := self;
	preempt_disable();
}

macro task_rq_unlock(p)
{
	(* XXX that task can have moved rq's !! *)
	pi_locks[p] := NULL;
	preempt_enable();
}

macro __migrate_task(rq, p, dest_cpu)
{
	(* Affinity changing is valid, check it before moving  *)
	if (dest_cpu \in task_structs[p].cpus_mask) {
		runqueues[rq]       := runqueues[rq]       \ {p} ||
		runqueues[dest_cpu] := runqueues[dest_cpu] \union {p};

		task_cpu[p] := dest_cpu;
	}
}

(* procedures *)

procedure migrate_task(p, dest_cpu)
{
mt0:
       (*
	* Pick a migrate_disable task which is
	* - Not migration disabled
	* - Not running
	* - Queued on a different CPU
	*)
	task_rq_lock(p);
mt1:
	if (/\ ~task_structs[MD_TASK].migration_disabled
	    /\ \A cpu \in CPUS: ~task_running(cpu, MD_TASK)
	    /\ task_cpu[MD_TASK] # self[2]) {
		__migrate_task(task_cpu[p], p, dest_cpu);
	};

mt2:
	task_rq_unlock(p);
	return;
}

(*
 * Doesn't bother with hotplug (online vs active masks)
 * Doesn't bother with p->cpus_mask vs p->cpus_ptr
 *)
procedure set_cpus_allowed_ptr(p, mask, enable_migration)
variables pending_ref; complete = FALSE; rq_cpu; dest_cpu;
{
sca0:
	assert NonReentrantSCA(self);

	(* Init the pseudo stack variables *)
	my_pending[self]   := MY_PENDING_INIT;
	stopper_wait[self] := FALSE;

	task_rq_lock(p);
	rq_cpu := task_cpu[p];
sca1:
	if ((~enable_migration) /\ task_structs[p].cpus_mask = mask) {
		task_rq_unlock(p);
		return;
	};
sca2:
	(* enable_migration only flips ->cpus_ptr, which we don't model here *)
	if (~enable_migration)
		task_structs[p].cpus_mask := mask;

	with (cpu \in task_structs[p].cpus_mask;)
		dest_cpu := cpu;

	(* affine_move_task() starts here *)
sca3:
	if (task_cpu[p] \in task_structs[p].cpus_mask) {
		pending_ref := task_structs[p].pending_ref;
sca4:
		if (pending_ref # NULL) {
			my_pending[pending_ref].refcount := my_pending[pending_ref].refcount + 1;
			task_structs[p].pending_ref := NULL;
			complete := TRUE;
		};

		task_rq_unlock(p);
sca5:
		if (complete)
			goto do_complete;
sca6:
		return;
	};
sca7:
	if (~enable_migration) {
		if (task_structs[p].pending_ref = NULL) {
			task_structs[p].pending_ref := self;
			my_pending[self].completed := FALSE ||
			my_pending[self].refcount := 1;
		} else {
			my_pending[task_structs[p].pending_ref].refcount :=
				my_pending[task_structs[p].pending_ref].refcount + 1;
		}
	};
sca8:
	(* ~enable_migration, see above. *)
	(* enable_migration: can only get here if !local, means previous request *)
	assert task_structs[p].pending_ref # NULL;
	pending_ref := task_structs[p].pending_ref;
sca9:
	if (enable_migration) {
		my_pending[pending_ref].refcount := my_pending[pending_ref].refcount + 1;
		task_rq_unlock(p);
sca10:
		stop_one_cpu_nowait(rq_cpu,
			[p |-> p, pending |-> pending_ref, dest_cpu |-> NULL, wait |-> NULL]);
		return;
	};

sca11:
	if (task_running(rq_cpu, p)) {
		my_pending[pending_ref].refcount := my_pending[pending_ref].refcount + 1;
		task_rq_unlock(p);
sca12:
		(*
		 * Waiting version needs to be split over 2 labels (i.e. steps),
		 * so just reuse the nowait + an await.
		 *)
		stop_one_cpu_nowait(rq_cpu,
			[p |-> p, pending |-> pending_ref, dest_cpu |-> NULL, wait |-> NULL]);
(* sca13: *)
(*		await stopper_wait[self]; *)
	} else {
		if (~is_migration_disabled(p)) {
			if (task_on_rq_queued(p))
				__migrate_task(rq_cpu, p, dest_cpu);

			task_structs[p].pending_ref := NULL;
			complete := TRUE;
		};

		task_rq_unlock(p);

do_complete:
		if (complete)
			my_pending[pending_ref].completed := TRUE;
	};

sca14:
	await my_pending[pending_ref].completed;
	my_pending[pending_ref].refcount := my_pending[pending_ref].refcount - 1;
sca15:
	await my_pending[self].refcount = 0;

	(* Assert no dangling ref on my_pending *)
	assert ~ (\E tsk \in TASKS \ {self}: task_structs[tsk].pending_ref = self);

	return;
}

procedure migrate_disable()
{

md0:
	preempt_disable();
md1:
	assert ~ task_structs[self].migration_disabled;
	task_structs[self].migration_disabled := TRUE;

md2:
	preempt_enable();
	return;
}

procedure migrate_enable()
{
me0:
	preempt_disable();

	call set_cpus_allowed_ptr(self, {}, TRUE);
me1:
	task_structs[self].migration_disabled := FALSE;
me2:
	preempt_enable();
	return;
}

(* processes *)

(*
 * The "victim" thread that can be Migration-Disabled.
 *)
fair process (md \in {MD_TASK})
{
mdt0:
	while (TRUE) {
mdt1:
		call migrate_disable();
mdt2:
		skip;
mdt3:
		call migrate_enable();
	}
}

(*
 * Threads repeatedly fighting over the affinity of MD_TASK.
 *)
fair process (aff \in AFFINER_TASKS)
{
affloop:
	while (TRUE) {
	      with (msk \in SUBSET(CPUS) \ {{}})
		   call set_cpus_allowed_ptr(MD_TASK, msk, FALSE);
	}
}

(*
 * The stopper threads. Here they only do migration_cpu_stop().
 *)
fair process (stop \in STOPPER_TASKS)
variables do_complete; work; p_pending;
{
st0:
	while (TRUE) {
st1:
		while (~stopper_has_work(self[2]))
		      sleep();
st2:
		do_complete := FALSE;
		(* Pop the head of the list *)
		work := Head(stopper_work[self[2]]) ||
		stopper_work[self[2]] := Tail(stopper_work[self[2]]);
lock:
		task_rq_lock(work.p);

		p_pending := task_structs[work.p].pending_ref;
st3:
		if (task_cpu[work.p] = self[2]) {
			if (is_migration_disabled(work.p))
				goto out;
st4:
			if (p_pending # NULL) {
				task_structs[work.p].pending_ref := NULL;
				do_complete := TRUE;
			};
st5:
			if (work.dest_cpu = NULL) {
				if (p_pending = NULL)
					goto out;
any:
				with (dest \in task_structs[work.p].cpus_mask)
					work.dest_cpu := dest;
			};

(*			if ((work.dest_cpu = NULL \/ work.dest_cpu = self[2]) /\ p_pending = NULL) *)
(*			       goto out; *)
(* any: *)
(*			if (work.dest_cpu = NULL \/ work.dest_cpu \notin task_structs[work.p].cpus_mask) *)
(*			       with (dest \in task_structs[work.p].cpus_mask) *)
(*				       work.dest_cpu := dest; *)

st6:
			if (task_on_rq_queued(work.p))
				__migrate_task(self[2], work.p, work.dest_cpu);
			(* XXX: else, when MD_TASK can sleep *)

		} else if (work.dest_cpu = NULL \/ p_pending # NULL) {
		       (* XXX must be ptr, not mask! *)
			if (p_pending # NULL /\ task_cpu[work.p] \in task_structs[work.p].cpus_mask) {
				task_structs[work.p].pending_ref := NULL;
				do_complete := TRUE;
				goto out;
			};
st77:
			if (p_pending = NULL)
				goto out;
st7:
			task_rq_unlock(work.p);
st8:
			stop_one_cpu_nowait(task_cpu[work.p], work);
			goto comp;
		}; (* else { *)
		(*	assert p_pending = NULL; *)
		(* }; *)

out:
		task_rq_unlock(work.p);
st9:
		if (do_complete)
			my_pending[p_pending].completed := TRUE;
dec:
		if (work.pending # NULL)
			my_pending[work.pending].refcount := my_pending[work.pending].refcount - 1;
comp:
		if (work.wait # NULL)
			stopper_wait[work.wait] := TRUE;
	}
}

fair process (hpio \in HPRIO_TASKS)
{
pr0:
	while (TRUE) {
	      either
		    sleep();
	      or
		    skip;
	}
}

(*
 * "Fake" tick threads. Their goal is to let some actions happen "anytime",
 * IOW be interleaved with any other step of the spec. Said actions are:
 * - Waking up a "high-prio" task to preempt the Migrate-Disabled task
 * - Migrating an MD_TASK
 * - Running schedule()
 *)
fair process (tick \in TICK_TASKS)
{
t0:
	while (TRUE) {
		either {
			skip;
		} or {
			wake(PCPU_TASK(HPRIO_TASK, self[2]));
		} or {
			call migrate_task(MD_TASK, self[2]);
		};
t1:
		if (preempt_count[currents[self[2]]] = 0)
			__schedule(self[2]);
	      (* TODO: move MD_TASK if !running && !migration_disabled *)
	}
}

} *)
\* BEGIN TRANSLATION
\* Label do_complete of procedure set_cpus_allowed_ptr at line 380 col 17 changed to do_complete_
\* Procedure variable dest_cpu of procedure set_cpus_allowed_ptr at line 287 col 50 changed to dest_cpu_
\* Parameter p of procedure migrate_task at line 260 col 24 changed to p_
CONSTANT defaultInitValue
VARIABLES task_structs, preempt_count, task_cpu, runqueues, currents, 
          my_pending, stopper_wait, pi_locks, stopper_work, pc, stack

(* define statement *)
task_on_rq_queued(p) == \E cpu \in CPUS : p \in runqueues[cpu]
task_running(cpu, p) == currents[cpu] = p

is_migration_disabled(p) == task_structs[p].migration_disabled

stopper_has_work(cpu) == Len(stopper_work[cpu]) > 0



MY_PENDING_INIT    == [completed |-> FALSE, refcount |-> 0]
MIGRATION_ARG_INIT ==  [
        p        |-> NULL,
        pending  |-> NULL,
        dest_cpu |-> NULL,
        done     |-> FALSE
]

TaskStructType == task_structs \in [TASKS ->
        [migration_disabled : BOOLEAN,
         cpus_mask          : (SUBSET CPUS) \ {},
         pending_ref        : TASKS \union {NULL},
         prio               : Nat]
]

TypesOK ==
        /\ \A tsk \in SCHED_TASKS : task_cpu[tsk] \in CPUS

        /\ preempt_count \in [TASKS -> Nat]

        /\ \A cpu \in CPUS :
          /\ \A id \in DOMAIN stopper_work[cpu] : stopper_work[cpu][id] \in
                [p        : TASKS \union {NULL},
                 pending  : TASKS \union {NULL},
                 dest_cpu : CPUS \union {NULL},
                 wait     : TASKS \union {NULL}]
          /\ runqueues[cpu] \subseteq SCHED_TASKS
          /\ currents[cpu] \in SCHED_TASKS

        /\ my_pending \in [TASKS -> [completed : BOOLEAN, refcount : Nat]]
        /\ pi_locks \in [TASKS -> TASKS \union {NULL}]


ProcessEnabled(self) ==
        IF self \notin SCHED_TASKS THEN TRUE
        ELSE \E cpu \in CPUS : currents[cpu] = self



RefcountOK == \A task \in TASKS: my_pending[task].refcount >= 0


AffinityOK ==
        \A cpu \in CPUS :
          (MD_TASK = currents[cpu] /\ task_structs[MD_TASK].pending_ref = NULL) =>
            \/ cpu \in task_structs[MD_TASK].cpus_mask









            \/ pi_locks[MD_TASK] \in TASKS

QueuesOK ==
        \A a, b \in CPUS:
          /\ currents[a] \in runqueues[a]
          /\ a # b =>

            /\ currents[a] # currents[b]

            /\ runqueues[a] \cap runqueues[b] = {}

NonReentrantSCA(self) ==
        \E id \in DOMAIN stack[self] : stack[self][id].procedure = "set_cpus_allowed_ptr" =>
            \A other \in DOMAIN stack[self] \ {id} :
              stack[self][other].procedure # "set_cpus_allowed_ptr"


Perms == Permutations(CPUS) \union Permutations(AFFINER_TASKS)

VARIABLES p_, dest_cpu, p, mask, enable_migration, pending_ref, complete, 
          rq_cpu, dest_cpu_, do_complete, work, p_pending

vars == << task_structs, preempt_count, task_cpu, runqueues, currents, 
           my_pending, stopper_wait, pi_locks, stopper_work, pc, stack, p_, 
           dest_cpu, p, mask, enable_migration, pending_ref, complete, rq_cpu, 
           dest_cpu_, do_complete, work, p_pending >>

ProcSet == ({MD_TASK}) \cup (AFFINER_TASKS) \cup (STOPPER_TASKS) \cup (HPRIO_TASKS) \cup (TICK_TASKS)

Init == (* Global variables *)
        /\ task_structs =                [tsk \in TASKS |->
                          
                                     [migration_disabled |-> FALSE,
                                     cpus_mask           |->
                                          IF tsk \in PCPU_TASKS THEN {PCPU_TASK_CPU(tsk)}
                                          ELSE                     CPUS,
                                     pending_ref         |-> NULL,
                                     prio                |->
                                          IF      tsk \in STOPPER_TASKS THEN 3
                                          ELSE IF tsk \in HPRIO_TASKS   THEN 2
                                          ELSE IF tsk = MD_TASK       THEN 1
                                          ELSE                             0]
                          ]
        /\ preempt_count = [tsk \in TASKS |-> 0]
        /\ task_cpu = [tsk \in SCHED_TASKS |->
                          IF tsk \in PCPU_TASKS THEN PCPU_TASK_CPU(tsk)
                          ELSE                     INIT_CPU
                      ]
        /\ runqueues = [cpu \in CPUS |->
                           {PCPU_TASK(IDLE_TASK, cpu)} \union
                           IF cpu = INIT_CPU THEN {MD_TASK} ELSE {}
                       ]
        /\ currents = [cpu \in CPUS |->
                          IF cpu = INIT_CPU THEN MD_TASK
                          ELSE            PCPU_TASK(IDLE_TASK, cpu)
                      ]
        /\ my_pending = [tsk \in TASKS |-> MY_PENDING_INIT]
        /\ stopper_wait = [tsk \in TASKS |-> FALSE]
        /\ pi_locks = [tsk \in TASKS |-> NULL]
        /\ stopper_work = [ cpu \in CPUS |-> << >> ]
        (* Procedure migrate_task *)
        /\ p_ = [ self \in ProcSet |-> defaultInitValue]
        /\ dest_cpu = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure set_cpus_allowed_ptr *)
        /\ p = [ self \in ProcSet |-> defaultInitValue]
        /\ mask = [ self \in ProcSet |-> defaultInitValue]
        /\ enable_migration = [ self \in ProcSet |-> defaultInitValue]
        /\ pending_ref = [ self \in ProcSet |-> defaultInitValue]
        /\ complete = [ self \in ProcSet |-> FALSE]
        /\ rq_cpu = [ self \in ProcSet |-> defaultInitValue]
        /\ dest_cpu_ = [ self \in ProcSet |-> defaultInitValue]
        (* Process stop *)
        /\ do_complete = [self \in STOPPER_TASKS |-> defaultInitValue]
        /\ work = [self \in STOPPER_TASKS |-> defaultInitValue]
        /\ p_pending = [self \in STOPPER_TASKS |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in {MD_TASK} -> "mdt0"
                                        [] self \in AFFINER_TASKS -> "affloop"
                                        [] self \in STOPPER_TASKS -> "st0"
                                        [] self \in HPRIO_TASKS -> "pr0"
                                        [] self \in TICK_TASKS -> "t0"]

mt0(self) == /\ pc[self] = "mt0" /\ ProcessEnabled(self)
             /\ pi_locks[p_[self]] = NULL
             /\ pi_locks' = [pi_locks EXCEPT ![p_[self]] = self]
             /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] + 1]
             /\ pc' = [pc EXCEPT ![self] = "mt1"]
             /\ UNCHANGED << task_structs, task_cpu, runqueues, currents, 
                             my_pending, stopper_wait, stopper_work, stack, p_, 
                             dest_cpu, p, mask, enable_migration, pending_ref, 
                             complete, rq_cpu, dest_cpu_, do_complete, work, 
                             p_pending >>

mt1(self) == /\ pc[self] = "mt1" /\ ProcessEnabled(self)
             /\ IF /\ ~task_structs[MD_TASK].migration_disabled
                   /\ \A cpu \in CPUS: ~task_running(cpu, MD_TASK)
                   /\ task_cpu[MD_TASK] # self[2]
                   THEN /\ IF dest_cpu[self] \in task_structs[p_[self]].cpus_mask
                              THEN /\ runqueues' = [runqueues EXCEPT ![(task_cpu[p_[self]])] = runqueues[(task_cpu[p_[self]])]       \ {p_[self]},
                                                                     ![dest_cpu[self]] = runqueues[dest_cpu[self]] \union {p_[self]}]
                                   /\ task_cpu' = [task_cpu EXCEPT ![p_[self]] = dest_cpu[self]]
                              ELSE /\ TRUE
                                   /\ UNCHANGED << task_cpu, runqueues >>
                   ELSE /\ TRUE
                        /\ UNCHANGED << task_cpu, runqueues >>
             /\ pc' = [pc EXCEPT ![self] = "mt2"]
             /\ UNCHANGED << task_structs, preempt_count, currents, my_pending, 
                             stopper_wait, pi_locks, stopper_work, stack, p_, 
                             dest_cpu, p, mask, enable_migration, pending_ref, 
                             complete, rq_cpu, dest_cpu_, do_complete, work, 
                             p_pending >>

mt2(self) == /\ pc[self] = "mt2" /\ ProcessEnabled(self)
             /\ pi_locks' = [pi_locks EXCEPT ![p_[self]] = NULL]
             /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] - 1]
             /\ IF self \in SCHED_TASKS /\ preempt_count'[self] = 0
                   THEN /\ \E tsk \in         {t \in runqueues[(CHOOSE cpu \in CPUS : currents[cpu] = self)] : \A other \in runqueues[(CHOOSE cpu \in CPUS : currents[cpu] = self)] \ {t} :
                                      task_structs[t].prio >= task_structs[other].prio}:
                             currents' = [currents EXCEPT ![(CHOOSE cpu \in CPUS : currents[cpu] = self)] = tsk]
                   ELSE /\ TRUE
                        /\ UNCHANGED currents
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ p_' = [p_ EXCEPT ![self] = Head(stack[self]).p_]
             /\ dest_cpu' = [dest_cpu EXCEPT ![self] = Head(stack[self]).dest_cpu]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << task_structs, task_cpu, runqueues, my_pending, 
                             stopper_wait, stopper_work, p, mask, 
                             enable_migration, pending_ref, complete, rq_cpu, 
                             dest_cpu_, do_complete, work, p_pending >>

migrate_task(self) == mt0(self) \/ mt1(self) \/ mt2(self)

sca0(self) == /\ pc[self] = "sca0" /\ ProcessEnabled(self)
              /\ Assert(NonReentrantSCA(self), 
                        "Failure of assertion at line 290, column 9.")
              /\ my_pending' = [my_pending EXCEPT ![self] = MY_PENDING_INIT]
              /\ stopper_wait' = [stopper_wait EXCEPT ![self] = FALSE]
              /\ pi_locks[p[self]] = NULL
              /\ pi_locks' = [pi_locks EXCEPT ![p[self]] = self]
              /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] + 1]
              /\ rq_cpu' = [rq_cpu EXCEPT ![self] = task_cpu[p[self]]]
              /\ pc' = [pc EXCEPT ![self] = "sca1"]
              /\ UNCHANGED << task_structs, task_cpu, runqueues, currents, 
                              stopper_work, stack, p_, dest_cpu, p, mask, 
                              enable_migration, pending_ref, complete, 
                              dest_cpu_, do_complete, work, p_pending >>

sca1(self) == /\ pc[self] = "sca1" /\ ProcessEnabled(self)
              /\ IF (~enable_migration[self]) /\ task_structs[p[self]].cpus_mask = mask[self]
                    THEN /\ pi_locks' = [pi_locks EXCEPT ![p[self]] = NULL]
                         /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] - 1]
                         /\ IF self \in SCHED_TASKS /\ preempt_count'[self] = 0
                               THEN /\ \E tsk \in         {t \in runqueues[(CHOOSE cpu \in CPUS : currents[cpu] = self)] : \A other \in runqueues[(CHOOSE cpu \in CPUS : currents[cpu] = self)] \ {t} :
                                                  task_structs[t].prio >= task_structs[other].prio}:
                                         currents' = [currents EXCEPT ![(CHOOSE cpu \in CPUS : currents[cpu] = self)] = tsk]
                               ELSE /\ TRUE
                                    /\ UNCHANGED currents
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ pending_ref' = [pending_ref EXCEPT ![self] = Head(stack[self]).pending_ref]
                         /\ complete' = [complete EXCEPT ![self] = Head(stack[self]).complete]
                         /\ rq_cpu' = [rq_cpu EXCEPT ![self] = Head(stack[self]).rq_cpu]
                         /\ dest_cpu_' = [dest_cpu_ EXCEPT ![self] = Head(stack[self]).dest_cpu_]
                         /\ p' = [p EXCEPT ![self] = Head(stack[self]).p]
                         /\ mask' = [mask EXCEPT ![self] = Head(stack[self]).mask]
                         /\ enable_migration' = [enable_migration EXCEPT ![self] = Head(stack[self]).enable_migration]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "sca2"]
                         /\ UNCHANGED << preempt_count, currents, pi_locks, 
                                         stack, p, mask, enable_migration, 
                                         pending_ref, complete, rq_cpu, 
                                         dest_cpu_ >>
              /\ UNCHANGED << task_structs, task_cpu, runqueues, my_pending, 
                              stopper_wait, stopper_work, p_, dest_cpu, 
                              do_complete, work, p_pending >>

sca2(self) == /\ pc[self] = "sca2" /\ ProcessEnabled(self)
              /\ IF ~enable_migration[self]
                    THEN /\ task_structs' = [task_structs EXCEPT ![p[self]].cpus_mask = mask[self]]
                    ELSE /\ TRUE
                         /\ UNCHANGED task_structs
              /\ \E cpu \in task_structs'[p[self]].cpus_mask:
                   dest_cpu_' = [dest_cpu_ EXCEPT ![self] = cpu]
              /\ pc' = [pc EXCEPT ![self] = "sca3"]
              /\ UNCHANGED << preempt_count, task_cpu, runqueues, currents, 
                              my_pending, stopper_wait, pi_locks, stopper_work, 
                              stack, p_, dest_cpu, p, mask, enable_migration, 
                              pending_ref, complete, rq_cpu, do_complete, work, 
                              p_pending >>

sca3(self) == /\ pc[self] = "sca3" /\ ProcessEnabled(self)
              /\ IF task_cpu[p[self]] \in task_structs[p[self]].cpus_mask
                    THEN /\ pending_ref' = [pending_ref EXCEPT ![self] = task_structs[p[self]].pending_ref]
                         /\ pc' = [pc EXCEPT ![self] = "sca4"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "sca7"]
                         /\ UNCHANGED pending_ref
              /\ UNCHANGED << task_structs, preempt_count, task_cpu, runqueues, 
                              currents, my_pending, stopper_wait, pi_locks, 
                              stopper_work, stack, p_, dest_cpu, p, mask, 
                              enable_migration, complete, rq_cpu, dest_cpu_, 
                              do_complete, work, p_pending >>

sca4(self) == /\ pc[self] = "sca4" /\ ProcessEnabled(self)
              /\ IF pending_ref[self] # NULL
                    THEN /\ my_pending' = [my_pending EXCEPT ![pending_ref[self]].refcount = my_pending[pending_ref[self]].refcount + 1]
                         /\ task_structs' = [task_structs EXCEPT ![p[self]].pending_ref = NULL]
                         /\ complete' = [complete EXCEPT ![self] = TRUE]
                    ELSE /\ TRUE
                         /\ UNCHANGED << task_structs, my_pending, complete >>
              /\ pi_locks' = [pi_locks EXCEPT ![p[self]] = NULL]
              /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] - 1]
              /\ IF self \in SCHED_TASKS /\ preempt_count'[self] = 0
                    THEN /\ \E tsk \in         {t \in runqueues[(CHOOSE cpu \in CPUS : currents[cpu] = self)] : \A other \in runqueues[(CHOOSE cpu \in CPUS : currents[cpu] = self)] \ {t} :
                                       task_structs'[t].prio >= task_structs'[other].prio}:
                              currents' = [currents EXCEPT ![(CHOOSE cpu \in CPUS : currents[cpu] = self)] = tsk]
                    ELSE /\ TRUE
                         /\ UNCHANGED currents
              /\ pc' = [pc EXCEPT ![self] = "sca5"]
              /\ UNCHANGED << task_cpu, runqueues, stopper_wait, stopper_work, 
                              stack, p_, dest_cpu, p, mask, enable_migration, 
                              pending_ref, rq_cpu, dest_cpu_, do_complete, 
                              work, p_pending >>

sca5(self) == /\ pc[self] = "sca5" /\ ProcessEnabled(self)
              /\ IF complete[self]
                    THEN /\ pc' = [pc EXCEPT ![self] = "do_complete_"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "sca6"]
              /\ UNCHANGED << task_structs, preempt_count, task_cpu, runqueues, 
                              currents, my_pending, stopper_wait, pi_locks, 
                              stopper_work, stack, p_, dest_cpu, p, mask, 
                              enable_migration, pending_ref, complete, rq_cpu, 
                              dest_cpu_, do_complete, work, p_pending >>

sca6(self) == /\ pc[self] = "sca6" /\ ProcessEnabled(self)
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ pending_ref' = [pending_ref EXCEPT ![self] = Head(stack[self]).pending_ref]
              /\ complete' = [complete EXCEPT ![self] = Head(stack[self]).complete]
              /\ rq_cpu' = [rq_cpu EXCEPT ![self] = Head(stack[self]).rq_cpu]
              /\ dest_cpu_' = [dest_cpu_ EXCEPT ![self] = Head(stack[self]).dest_cpu_]
              /\ p' = [p EXCEPT ![self] = Head(stack[self]).p]
              /\ mask' = [mask EXCEPT ![self] = Head(stack[self]).mask]
              /\ enable_migration' = [enable_migration EXCEPT ![self] = Head(stack[self]).enable_migration]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << task_structs, preempt_count, task_cpu, runqueues, 
                              currents, my_pending, stopper_wait, pi_locks, 
                              stopper_work, p_, dest_cpu, do_complete, work, 
                              p_pending >>

sca7(self) == /\ pc[self] = "sca7" /\ ProcessEnabled(self)
              /\ IF ~enable_migration[self]
                    THEN /\ IF task_structs[p[self]].pending_ref = NULL
                               THEN /\ task_structs' = [task_structs EXCEPT ![p[self]].pending_ref = self]
                                    /\ my_pending' = [my_pending EXCEPT ![self].completed = FALSE,
                                                                        ![self].refcount = 1]
                               ELSE /\ my_pending' = [my_pending EXCEPT ![task_structs[p[self]].pending_ref].refcount = my_pending[task_structs[p[self]].pending_ref].refcount + 1]
                                    /\ UNCHANGED task_structs
                    ELSE /\ TRUE
                         /\ UNCHANGED << task_structs, my_pending >>
              /\ pc' = [pc EXCEPT ![self] = "sca8"]
              /\ UNCHANGED << preempt_count, task_cpu, runqueues, currents, 
                              stopper_wait, pi_locks, stopper_work, stack, p_, 
                              dest_cpu, p, mask, enable_migration, pending_ref, 
                              complete, rq_cpu, dest_cpu_, do_complete, work, 
                              p_pending >>

sca8(self) == /\ pc[self] = "sca8" /\ ProcessEnabled(self)
              /\ Assert(task_structs[p[self]].pending_ref # NULL, 
                        "Failure of assertion at line 343, column 9.")
              /\ pending_ref' = [pending_ref EXCEPT ![self] = task_structs[p[self]].pending_ref]
              /\ pc' = [pc EXCEPT ![self] = "sca9"]
              /\ UNCHANGED << task_structs, preempt_count, task_cpu, runqueues, 
                              currents, my_pending, stopper_wait, pi_locks, 
                              stopper_work, stack, p_, dest_cpu, p, mask, 
                              enable_migration, complete, rq_cpu, dest_cpu_, 
                              do_complete, work, p_pending >>

sca9(self) == /\ pc[self] = "sca9" /\ ProcessEnabled(self)
              /\ IF enable_migration[self]
                    THEN /\ my_pending' = [my_pending EXCEPT ![pending_ref[self]].refcount = my_pending[pending_ref[self]].refcount + 1]
                         /\ pi_locks' = [pi_locks EXCEPT ![p[self]] = NULL]
                         /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] - 1]
                         /\ IF self \in SCHED_TASKS /\ preempt_count'[self] = 0
                               THEN /\ \E tsk \in         {t \in runqueues[(CHOOSE cpu \in CPUS : currents[cpu] = self)] : \A other \in runqueues[(CHOOSE cpu \in CPUS : currents[cpu] = self)] \ {t} :
                                                  task_structs[t].prio >= task_structs[other].prio}:
                                         currents' = [currents EXCEPT ![(CHOOSE cpu \in CPUS : currents[cpu] = self)] = tsk]
                               ELSE /\ TRUE
                                    /\ UNCHANGED currents
                         /\ pc' = [pc EXCEPT ![self] = "sca10"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "sca11"]
                         /\ UNCHANGED << preempt_count, currents, my_pending, 
                                         pi_locks >>
              /\ UNCHANGED << task_structs, task_cpu, runqueues, stopper_wait, 
                              stopper_work, stack, p_, dest_cpu, p, mask, 
                              enable_migration, pending_ref, complete, rq_cpu, 
                              dest_cpu_, do_complete, work, p_pending >>

sca10(self) == /\ pc[self] = "sca10" /\ ProcessEnabled(self)
               /\ stopper_work' = [stopper_work EXCEPT ![rq_cpu[self]] = Append(stopper_work[rq_cpu[self]], ([p |-> p[self], pending |-> pending_ref[self], dest_cpu |-> NULL, wait |-> NULL]))]
               /\ Assert(~task_structs[(PCPU_TASK(STOPPER_TASK, rq_cpu[self]))].migration_disabled, 
                         "Failure of assertion at line 191, column 9 of macro called at line 350, column 17.")
               /\ \E cpu \in task_structs[(PCPU_TASK(STOPPER_TASK, rq_cpu[self]))].cpus_mask:
                    /\ task_cpu' = [task_cpu EXCEPT ![(PCPU_TASK(STOPPER_TASK, rq_cpu[self]))] = rq_cpu[self]]
                    /\ runqueues' = [runqueues EXCEPT ![rq_cpu[self]] = runqueues[rq_cpu[self]] \union {(PCPU_TASK(STOPPER_TASK, rq_cpu[self]))}]
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ pending_ref' = [pending_ref EXCEPT ![self] = Head(stack[self]).pending_ref]
               /\ complete' = [complete EXCEPT ![self] = Head(stack[self]).complete]
               /\ rq_cpu' = [rq_cpu EXCEPT ![self] = Head(stack[self]).rq_cpu]
               /\ dest_cpu_' = [dest_cpu_ EXCEPT ![self] = Head(stack[self]).dest_cpu_]
               /\ p' = [p EXCEPT ![self] = Head(stack[self]).p]
               /\ mask' = [mask EXCEPT ![self] = Head(stack[self]).mask]
               /\ enable_migration' = [enable_migration EXCEPT ![self] = Head(stack[self]).enable_migration]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << task_structs, preempt_count, currents, 
                               my_pending, stopper_wait, pi_locks, p_, 
                               dest_cpu, do_complete, work, p_pending >>

sca11(self) == /\ pc[self] = "sca11" /\ ProcessEnabled(self)
               /\ IF task_running(rq_cpu[self], p[self])
                     THEN /\ my_pending' = [my_pending EXCEPT ![pending_ref[self]].refcount = my_pending[pending_ref[self]].refcount + 1]
                          /\ pi_locks' = [pi_locks EXCEPT ![p[self]] = NULL]
                          /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] - 1]
                          /\ IF self \in SCHED_TASKS /\ preempt_count'[self] = 0
                                THEN /\ \E tsk \in         {t \in runqueues[(CHOOSE cpu \in CPUS : currents[cpu] = self)] : \A other \in runqueues[(CHOOSE cpu \in CPUS : currents[cpu] = self)] \ {t} :
                                                   task_structs[t].prio >= task_structs[other].prio}:
                                          currents' = [currents EXCEPT ![(CHOOSE cpu \in CPUS : currents[cpu] = self)] = tsk]
                                ELSE /\ TRUE
                                     /\ UNCHANGED currents
                          /\ pc' = [pc EXCEPT ![self] = "sca12"]
                          /\ UNCHANGED << task_structs, task_cpu, runqueues, 
                                          complete >>
                     ELSE /\ IF ~is_migration_disabled(p[self])
                                THEN /\ IF task_on_rq_queued(p[self])
                                           THEN /\ IF dest_cpu_[self] \in task_structs[p[self]].cpus_mask
                                                      THEN /\ runqueues' = [runqueues EXCEPT ![rq_cpu[self]] = runqueues[rq_cpu[self]]       \ {p[self]},
                                                                                             ![dest_cpu_[self]] = runqueues[dest_cpu_[self]] \union {p[self]}]
                                                           /\ task_cpu' = [task_cpu EXCEPT ![p[self]] = dest_cpu_[self]]
                                                      ELSE /\ TRUE
                                                           /\ UNCHANGED << task_cpu, 
                                                                           runqueues >>
                                           ELSE /\ TRUE
                                                /\ UNCHANGED << task_cpu, 
                                                                runqueues >>
                                     /\ task_structs' = [task_structs EXCEPT ![p[self]].pending_ref = NULL]
                                     /\ complete' = [complete EXCEPT ![self] = TRUE]
                                ELSE /\ TRUE
                                     /\ UNCHANGED << task_structs, task_cpu, 
                                                     runqueues, complete >>
                          /\ pi_locks' = [pi_locks EXCEPT ![p[self]] = NULL]
                          /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] - 1]
                          /\ IF self \in SCHED_TASKS /\ preempt_count'[self] = 0
                                THEN /\ \E tsk \in         {t \in runqueues'[(CHOOSE cpu \in CPUS : currents[cpu] = self)] : \A other \in runqueues'[(CHOOSE cpu \in CPUS : currents[cpu] = self)] \ {t} :
                                                   task_structs'[t].prio >= task_structs'[other].prio}:
                                          currents' = [currents EXCEPT ![(CHOOSE cpu \in CPUS : currents[cpu] = self)] = tsk]
                                ELSE /\ TRUE
                                     /\ UNCHANGED currents
                          /\ pc' = [pc EXCEPT ![self] = "do_complete_"]
                          /\ UNCHANGED my_pending
               /\ UNCHANGED << stopper_wait, stopper_work, stack, p_, dest_cpu, 
                               p, mask, enable_migration, pending_ref, rq_cpu, 
                               dest_cpu_, do_complete, work, p_pending >>

sca12(self) == /\ pc[self] = "sca12" /\ ProcessEnabled(self)
               /\ stopper_work' = [stopper_work EXCEPT ![rq_cpu[self]] = Append(stopper_work[rq_cpu[self]], ([p |-> p[self], pending |-> pending_ref[self], dest_cpu |-> NULL, wait |-> NULL]))]
               /\ Assert(~task_structs[(PCPU_TASK(STOPPER_TASK, rq_cpu[self]))].migration_disabled, 
                         "Failure of assertion at line 191, column 9 of macro called at line 364, column 17.")
               /\ \E cpu \in task_structs[(PCPU_TASK(STOPPER_TASK, rq_cpu[self]))].cpus_mask:
                    /\ task_cpu' = [task_cpu EXCEPT ![(PCPU_TASK(STOPPER_TASK, rq_cpu[self]))] = rq_cpu[self]]
                    /\ runqueues' = [runqueues EXCEPT ![rq_cpu[self]] = runqueues[rq_cpu[self]] \union {(PCPU_TASK(STOPPER_TASK, rq_cpu[self]))}]
               /\ pc' = [pc EXCEPT ![self] = "sca14"]
               /\ UNCHANGED << task_structs, preempt_count, currents, 
                               my_pending, stopper_wait, pi_locks, stack, p_, 
                               dest_cpu, p, mask, enable_migration, 
                               pending_ref, complete, rq_cpu, dest_cpu_, 
                               do_complete, work, p_pending >>

do_complete_(self) == /\ pc[self] = "do_complete_" /\ ProcessEnabled(self)
                      /\ IF complete[self]
                            THEN /\ my_pending' = [my_pending EXCEPT ![pending_ref[self]].completed = TRUE]
                            ELSE /\ TRUE
                                 /\ UNCHANGED my_pending
                      /\ pc' = [pc EXCEPT ![self] = "sca14"]
                      /\ UNCHANGED << task_structs, preempt_count, task_cpu, 
                                      runqueues, currents, stopper_wait, 
                                      pi_locks, stopper_work, stack, p_, 
                                      dest_cpu, p, mask, enable_migration, 
                                      pending_ref, complete, rq_cpu, dest_cpu_, 
                                      do_complete, work, p_pending >>

sca14(self) == /\ pc[self] = "sca14" /\ ProcessEnabled(self)
               /\ my_pending[pending_ref[self]].completed
               /\ my_pending' = [my_pending EXCEPT ![pending_ref[self]].refcount = my_pending[pending_ref[self]].refcount - 1]
               /\ pc' = [pc EXCEPT ![self] = "sca15"]
               /\ UNCHANGED << task_structs, preempt_count, task_cpu, 
                               runqueues, currents, stopper_wait, pi_locks, 
                               stopper_work, stack, p_, dest_cpu, p, mask, 
                               enable_migration, pending_ref, complete, rq_cpu, 
                               dest_cpu_, do_complete, work, p_pending >>

sca15(self) == /\ pc[self] = "sca15" /\ ProcessEnabled(self)
               /\ my_pending[self].refcount = 0
               /\ Assert(~ (\E tsk \in TASKS \ {self}: task_structs[tsk].pending_ref = self), 
                         "Failure of assertion at line 391, column 9.")
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ pending_ref' = [pending_ref EXCEPT ![self] = Head(stack[self]).pending_ref]
               /\ complete' = [complete EXCEPT ![self] = Head(stack[self]).complete]
               /\ rq_cpu' = [rq_cpu EXCEPT ![self] = Head(stack[self]).rq_cpu]
               /\ dest_cpu_' = [dest_cpu_ EXCEPT ![self] = Head(stack[self]).dest_cpu_]
               /\ p' = [p EXCEPT ![self] = Head(stack[self]).p]
               /\ mask' = [mask EXCEPT ![self] = Head(stack[self]).mask]
               /\ enable_migration' = [enable_migration EXCEPT ![self] = Head(stack[self]).enable_migration]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << task_structs, preempt_count, task_cpu, 
                               runqueues, currents, my_pending, stopper_wait, 
                               pi_locks, stopper_work, p_, dest_cpu, 
                               do_complete, work, p_pending >>

set_cpus_allowed_ptr(self) == sca0(self) \/ sca1(self) \/ sca2(self)
                                 \/ sca3(self) \/ sca4(self) \/ sca5(self)
                                 \/ sca6(self) \/ sca7(self) \/ sca8(self)
                                 \/ sca9(self) \/ sca10(self)
                                 \/ sca11(self) \/ sca12(self)
                                 \/ do_complete_(self) \/ sca14(self)
                                 \/ sca15(self)

md0(self) == /\ pc[self] = "md0" /\ ProcessEnabled(self)
             /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] + 1]
             /\ pc' = [pc EXCEPT ![self] = "md1"]
             /\ UNCHANGED << task_structs, task_cpu, runqueues, currents, 
                             my_pending, stopper_wait, pi_locks, stopper_work, 
                             stack, p_, dest_cpu, p, mask, enable_migration, 
                             pending_ref, complete, rq_cpu, dest_cpu_, 
                             do_complete, work, p_pending >>

md1(self) == /\ pc[self] = "md1" /\ ProcessEnabled(self)
             /\ Assert(~ task_structs[self].migration_disabled, 
                       "Failure of assertion at line 402, column 9.")
             /\ task_structs' = [task_structs EXCEPT ![self].migration_disabled = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "md2"]
             /\ UNCHANGED << preempt_count, task_cpu, runqueues, currents, 
                             my_pending, stopper_wait, pi_locks, stopper_work, 
                             stack, p_, dest_cpu, p, mask, enable_migration, 
                             pending_ref, complete, rq_cpu, dest_cpu_, 
                             do_complete, work, p_pending >>

md2(self) == /\ pc[self] = "md2" /\ ProcessEnabled(self)
             /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] - 1]
             /\ IF self \in SCHED_TASKS /\ preempt_count'[self] = 0
                   THEN /\ \E tsk \in         {t \in runqueues[(CHOOSE cpu \in CPUS : currents[cpu] = self)] : \A other \in runqueues[(CHOOSE cpu \in CPUS : currents[cpu] = self)] \ {t} :
                                      task_structs[t].prio >= task_structs[other].prio}:
                             currents' = [currents EXCEPT ![(CHOOSE cpu \in CPUS : currents[cpu] = self)] = tsk]
                   ELSE /\ TRUE
                        /\ UNCHANGED currents
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << task_structs, task_cpu, runqueues, my_pending, 
                             stopper_wait, pi_locks, stopper_work, p_, 
                             dest_cpu, p, mask, enable_migration, pending_ref, 
                             complete, rq_cpu, dest_cpu_, do_complete, work, 
                             p_pending >>

migrate_disable(self) == md0(self) \/ md1(self) \/ md2(self)

me0(self) == /\ pc[self] = "me0" /\ ProcessEnabled(self)
             /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] + 1]
             /\ /\ enable_migration' = [enable_migration EXCEPT ![self] = TRUE]
                /\ mask' = [mask EXCEPT ![self] = {}]
                /\ p' = [p EXCEPT ![self] = self]
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "set_cpus_allowed_ptr",
                                                         pc        |->  "me1",
                                                         pending_ref |->  pending_ref[self],
                                                         complete  |->  complete[self],
                                                         rq_cpu    |->  rq_cpu[self],
                                                         dest_cpu_ |->  dest_cpu_[self],
                                                         p         |->  p[self],
                                                         mask      |->  mask[self],
                                                         enable_migration |->  enable_migration[self] ] >>
                                                     \o stack[self]]
             /\ pending_ref' = [pending_ref EXCEPT ![self] = defaultInitValue]
             /\ complete' = [complete EXCEPT ![self] = FALSE]
             /\ rq_cpu' = [rq_cpu EXCEPT ![self] = defaultInitValue]
             /\ dest_cpu_' = [dest_cpu_ EXCEPT ![self] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![self] = "sca0"]
             /\ UNCHANGED << task_structs, task_cpu, runqueues, currents, 
                             my_pending, stopper_wait, pi_locks, stopper_work, 
                             p_, dest_cpu, do_complete, work, p_pending >>

me1(self) == /\ pc[self] = "me1" /\ ProcessEnabled(self)
             /\ task_structs' = [task_structs EXCEPT ![self].migration_disabled = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "me2"]
             /\ UNCHANGED << preempt_count, task_cpu, runqueues, currents, 
                             my_pending, stopper_wait, pi_locks, stopper_work, 
                             stack, p_, dest_cpu, p, mask, enable_migration, 
                             pending_ref, complete, rq_cpu, dest_cpu_, 
                             do_complete, work, p_pending >>

me2(self) == /\ pc[self] = "me2" /\ ProcessEnabled(self)
             /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] - 1]
             /\ IF self \in SCHED_TASKS /\ preempt_count'[self] = 0
                   THEN /\ \E tsk \in         {t \in runqueues[(CHOOSE cpu \in CPUS : currents[cpu] = self)] : \A other \in runqueues[(CHOOSE cpu \in CPUS : currents[cpu] = self)] \ {t} :
                                      task_structs[t].prio >= task_structs[other].prio}:
                             currents' = [currents EXCEPT ![(CHOOSE cpu \in CPUS : currents[cpu] = self)] = tsk]
                   ELSE /\ TRUE
                        /\ UNCHANGED currents
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << task_structs, task_cpu, runqueues, my_pending, 
                             stopper_wait, pi_locks, stopper_work, p_, 
                             dest_cpu, p, mask, enable_migration, pending_ref, 
                             complete, rq_cpu, dest_cpu_, do_complete, work, 
                             p_pending >>

migrate_enable(self) == me0(self) \/ me1(self) \/ me2(self)

mdt0(self) == /\ pc[self] = "mdt0" /\ ProcessEnabled(self)
              /\ pc' = [pc EXCEPT ![self] = "mdt1"]
              /\ UNCHANGED << task_structs, preempt_count, task_cpu, runqueues, 
                              currents, my_pending, stopper_wait, pi_locks, 
                              stopper_work, stack, p_, dest_cpu, p, mask, 
                              enable_migration, pending_ref, complete, rq_cpu, 
                              dest_cpu_, do_complete, work, p_pending >>

mdt1(self) == /\ pc[self] = "mdt1" /\ ProcessEnabled(self)
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "migrate_disable",
                                                       pc        |->  "mdt2" ] >>
                                                   \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "md0"]
              /\ UNCHANGED << task_structs, preempt_count, task_cpu, runqueues, 
                              currents, my_pending, stopper_wait, pi_locks, 
                              stopper_work, p_, dest_cpu, p, mask, 
                              enable_migration, pending_ref, complete, rq_cpu, 
                              dest_cpu_, do_complete, work, p_pending >>

mdt2(self) == /\ pc[self] = "mdt2" /\ ProcessEnabled(self)
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "mdt3"]
              /\ UNCHANGED << task_structs, preempt_count, task_cpu, runqueues, 
                              currents, my_pending, stopper_wait, pi_locks, 
                              stopper_work, stack, p_, dest_cpu, p, mask, 
                              enable_migration, pending_ref, complete, rq_cpu, 
                              dest_cpu_, do_complete, work, p_pending >>

mdt3(self) == /\ pc[self] = "mdt3" /\ ProcessEnabled(self)
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "migrate_enable",
                                                       pc        |->  "mdt0" ] >>
                                                   \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "me0"]
              /\ UNCHANGED << task_structs, preempt_count, task_cpu, runqueues, 
                              currents, my_pending, stopper_wait, pi_locks, 
                              stopper_work, p_, dest_cpu, p, mask, 
                              enable_migration, pending_ref, complete, rq_cpu, 
                              dest_cpu_, do_complete, work, p_pending >>

md(self) == mdt0(self) \/ mdt1(self) \/ mdt2(self) \/ mdt3(self)

affloop(self) == /\ pc[self] = "affloop" /\ ProcessEnabled(self)
                 /\ \E msk \in SUBSET(CPUS) \ {{}}:
                      /\ /\ enable_migration' = [enable_migration EXCEPT ![self] = FALSE]
                         /\ mask' = [mask EXCEPT ![self] = msk]
                         /\ p' = [p EXCEPT ![self] = MD_TASK]
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "set_cpus_allowed_ptr",
                                                                  pc        |->  "affloop",
                                                                  pending_ref |->  pending_ref[self],
                                                                  complete  |->  complete[self],
                                                                  rq_cpu    |->  rq_cpu[self],
                                                                  dest_cpu_ |->  dest_cpu_[self],
                                                                  p         |->  p[self],
                                                                  mask      |->  mask[self],
                                                                  enable_migration |->  enable_migration[self] ] >>
                                                              \o stack[self]]
                      /\ pending_ref' = [pending_ref EXCEPT ![self] = defaultInitValue]
                      /\ complete' = [complete EXCEPT ![self] = FALSE]
                      /\ rq_cpu' = [rq_cpu EXCEPT ![self] = defaultInitValue]
                      /\ dest_cpu_' = [dest_cpu_ EXCEPT ![self] = defaultInitValue]
                      /\ pc' = [pc EXCEPT ![self] = "sca0"]
                 /\ UNCHANGED << task_structs, preempt_count, task_cpu, 
                                 runqueues, currents, my_pending, stopper_wait, 
                                 pi_locks, stopper_work, p_, dest_cpu, 
                                 do_complete, work, p_pending >>

aff(self) == affloop(self)

st0(self) == /\ pc[self] = "st0" /\ ProcessEnabled(self)
             /\ pc' = [pc EXCEPT ![self] = "st1"]
             /\ UNCHANGED << task_structs, preempt_count, task_cpu, runqueues, 
                             currents, my_pending, stopper_wait, pi_locks, 
                             stopper_work, stack, p_, dest_cpu, p, mask, 
                             enable_migration, pending_ref, complete, rq_cpu, 
                             dest_cpu_, do_complete, work, p_pending >>

st1(self) == /\ pc[self] = "st1" /\ ProcessEnabled(self)
             /\ IF ~stopper_has_work(self[2])
                   THEN /\ runqueues' = [runqueues EXCEPT ![task_cpu[self]] = runqueues[task_cpu[self]] \ {self}]
                        /\ \E tsk \in         {t \in runqueues'[(CHOOSE cpu \in CPUS : currents[cpu] = self)] : \A other \in runqueues'[(CHOOSE cpu \in CPUS : currents[cpu] = self)] \ {t} :
                                      task_structs[t].prio >= task_structs[other].prio}:
                             currents' = [currents EXCEPT ![(CHOOSE cpu \in CPUS : currents[cpu] = self)] = tsk]
                        /\ pc' = [pc EXCEPT ![self] = "st1"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "st2"]
                        /\ UNCHANGED << runqueues, currents >>
             /\ UNCHANGED << task_structs, preempt_count, task_cpu, my_pending, 
                             stopper_wait, pi_locks, stopper_work, stack, p_, 
                             dest_cpu, p, mask, enable_migration, pending_ref, 
                             complete, rq_cpu, dest_cpu_, do_complete, work, 
                             p_pending >>

st2(self) == /\ pc[self] = "st2" /\ ProcessEnabled(self)
             /\ do_complete' = [do_complete EXCEPT ![self] = FALSE]
             /\ /\ stopper_work' = [stopper_work EXCEPT ![self[2]] = Tail(stopper_work[self[2]])]
                /\ work' = [work EXCEPT ![self] = Head(stopper_work[self[2]])]
             /\ pc' = [pc EXCEPT ![self] = "lock"]
             /\ UNCHANGED << task_structs, preempt_count, task_cpu, runqueues, 
                             currents, my_pending, stopper_wait, pi_locks, 
                             stack, p_, dest_cpu, p, mask, enable_migration, 
                             pending_ref, complete, rq_cpu, dest_cpu_, 
                             p_pending >>

lock(self) == /\ pc[self] = "lock" /\ ProcessEnabled(self)
              /\ pi_locks[(work[self].p)] = NULL
              /\ pi_locks' = [pi_locks EXCEPT ![(work[self].p)] = self]
              /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] + 1]
              /\ p_pending' = [p_pending EXCEPT ![self] = task_structs[work[self].p].pending_ref]
              /\ pc' = [pc EXCEPT ![self] = "st3"]
              /\ UNCHANGED << task_structs, task_cpu, runqueues, currents, 
                              my_pending, stopper_wait, stopper_work, stack, 
                              p_, dest_cpu, p, mask, enable_migration, 
                              pending_ref, complete, rq_cpu, dest_cpu_, 
                              do_complete, work >>

st3(self) == /\ pc[self] = "st3" /\ ProcessEnabled(self)
             /\ IF task_cpu[work[self].p] = self[2]
                   THEN /\ IF is_migration_disabled(work[self].p)
                              THEN /\ pc' = [pc EXCEPT ![self] = "out"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "st4"]
                        /\ UNCHANGED << task_structs, do_complete >>
                   ELSE /\ IF work[self].dest_cpu = NULL \/ p_pending[self] # NULL
                              THEN /\ IF p_pending[self] # NULL /\ task_cpu[work[self].p] \in task_structs[work[self].p].cpus_mask
                                         THEN /\ task_structs' = [task_structs EXCEPT ![work[self].p].pending_ref = NULL]
                                              /\ do_complete' = [do_complete EXCEPT ![self] = TRUE]
                                              /\ pc' = [pc EXCEPT ![self] = "out"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "st77"]
                                              /\ UNCHANGED << task_structs, 
                                                              do_complete >>
                              ELSE /\ pc' = [pc EXCEPT ![self] = "out"]
                                   /\ UNCHANGED << task_structs, do_complete >>
             /\ UNCHANGED << preempt_count, task_cpu, runqueues, currents, 
                             my_pending, stopper_wait, pi_locks, stopper_work, 
                             stack, p_, dest_cpu, p, mask, enable_migration, 
                             pending_ref, complete, rq_cpu, dest_cpu_, work, 
                             p_pending >>

st4(self) == /\ pc[self] = "st4" /\ ProcessEnabled(self)
             /\ IF p_pending[self] # NULL
                   THEN /\ task_structs' = [task_structs EXCEPT ![work[self].p].pending_ref = NULL]
                        /\ do_complete' = [do_complete EXCEPT ![self] = TRUE]
                   ELSE /\ TRUE
                        /\ UNCHANGED << task_structs, do_complete >>
             /\ pc' = [pc EXCEPT ![self] = "st5"]
             /\ UNCHANGED << preempt_count, task_cpu, runqueues, currents, 
                             my_pending, stopper_wait, pi_locks, stopper_work, 
                             stack, p_, dest_cpu, p, mask, enable_migration, 
                             pending_ref, complete, rq_cpu, dest_cpu_, work, 
                             p_pending >>

st5(self) == /\ pc[self] = "st5" /\ ProcessEnabled(self)
             /\ IF work[self].dest_cpu = NULL
                   THEN /\ IF p_pending[self] = NULL
                              THEN /\ pc' = [pc EXCEPT ![self] = "out"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "any"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "st6"]
             /\ UNCHANGED << task_structs, preempt_count, task_cpu, runqueues, 
                             currents, my_pending, stopper_wait, pi_locks, 
                             stopper_work, stack, p_, dest_cpu, p, mask, 
                             enable_migration, pending_ref, complete, rq_cpu, 
                             dest_cpu_, do_complete, work, p_pending >>

any(self) == /\ pc[self] = "any" /\ ProcessEnabled(self)
             /\ \E dest \in task_structs[work[self].p].cpus_mask:
                  work' = [work EXCEPT ![self].dest_cpu = dest]
             /\ pc' = [pc EXCEPT ![self] = "st6"]
             /\ UNCHANGED << task_structs, preempt_count, task_cpu, runqueues, 
                             currents, my_pending, stopper_wait, pi_locks, 
                             stopper_work, stack, p_, dest_cpu, p, mask, 
                             enable_migration, pending_ref, complete, rq_cpu, 
                             dest_cpu_, do_complete, p_pending >>

st6(self) == /\ pc[self] = "st6" /\ ProcessEnabled(self)
             /\ IF task_on_rq_queued(work[self].p)
                   THEN /\ IF (work[self].dest_cpu) \in task_structs[(work[self].p)].cpus_mask
                              THEN /\ runqueues' = [runqueues EXCEPT ![(self[2])] = runqueues[(self[2])]       \ {(work[self].p)},
                                                                     ![(work[self].dest_cpu)] = runqueues[(work[self].dest_cpu)] \union {(work[self].p)}]
                                   /\ task_cpu' = [task_cpu EXCEPT ![(work[self].p)] = work[self].dest_cpu]
                              ELSE /\ TRUE
                                   /\ UNCHANGED << task_cpu, runqueues >>
                   ELSE /\ TRUE
                        /\ UNCHANGED << task_cpu, runqueues >>
             /\ pc' = [pc EXCEPT ![self] = "out"]
             /\ UNCHANGED << task_structs, preempt_count, currents, my_pending, 
                             stopper_wait, pi_locks, stopper_work, stack, p_, 
                             dest_cpu, p, mask, enable_migration, pending_ref, 
                             complete, rq_cpu, dest_cpu_, do_complete, work, 
                             p_pending >>

st77(self) == /\ pc[self] = "st77" /\ ProcessEnabled(self)
              /\ IF p_pending[self] = NULL
                    THEN /\ pc' = [pc EXCEPT ![self] = "out"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "st7"]
              /\ UNCHANGED << task_structs, preempt_count, task_cpu, runqueues, 
                              currents, my_pending, stopper_wait, pi_locks, 
                              stopper_work, stack, p_, dest_cpu, p, mask, 
                              enable_migration, pending_ref, complete, rq_cpu, 
                              dest_cpu_, do_complete, work, p_pending >>

st7(self) == /\ pc[self] = "st7" /\ ProcessEnabled(self)
             /\ pi_locks' = [pi_locks EXCEPT ![(work[self].p)] = NULL]
             /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] - 1]
             /\ IF self \in SCHED_TASKS /\ preempt_count'[self] = 0
                   THEN /\ \E tsk \in         {t \in runqueues[(CHOOSE cpu \in CPUS : currents[cpu] = self)] : \A other \in runqueues[(CHOOSE cpu \in CPUS : currents[cpu] = self)] \ {t} :
                                      task_structs[t].prio >= task_structs[other].prio}:
                             currents' = [currents EXCEPT ![(CHOOSE cpu \in CPUS : currents[cpu] = self)] = tsk]
                   ELSE /\ TRUE
                        /\ UNCHANGED currents
             /\ pc' = [pc EXCEPT ![self] = "st8"]
             /\ UNCHANGED << task_structs, task_cpu, runqueues, my_pending, 
                             stopper_wait, stopper_work, stack, p_, dest_cpu, 
                             p, mask, enable_migration, pending_ref, complete, 
                             rq_cpu, dest_cpu_, do_complete, work, p_pending >>

st8(self) == /\ pc[self] = "st8" /\ ProcessEnabled(self)
             /\ stopper_work' = [stopper_work EXCEPT ![(task_cpu[work[self].p])] = Append(stopper_work[(task_cpu[work[self].p])], work[self])]
             /\ Assert(~task_structs[(PCPU_TASK(STOPPER_TASK, (task_cpu[work[self].p])))].migration_disabled, 
                       "Failure of assertion at line 191, column 9 of macro called at line 516, column 25.")
             /\ \E cpu \in task_structs[(PCPU_TASK(STOPPER_TASK, (task_cpu[work[self].p])))].cpus_mask:
                  /\ task_cpu' = [task_cpu EXCEPT ![(PCPU_TASK(STOPPER_TASK, (task_cpu[work[self].p])))] = task_cpu[work[self].p]]
                  /\ runqueues' = [runqueues EXCEPT ![(task_cpu'[work[self].p])] = runqueues[(task_cpu'[work[self].p])] \union {(PCPU_TASK(STOPPER_TASK, (task_cpu'[work[self].p])))}]
             /\ pc' = [pc EXCEPT ![self] = "comp"]
             /\ UNCHANGED << task_structs, preempt_count, currents, my_pending, 
                             stopper_wait, pi_locks, stack, p_, dest_cpu, p, 
                             mask, enable_migration, pending_ref, complete, 
                             rq_cpu, dest_cpu_, do_complete, work, p_pending >>

out(self) == /\ pc[self] = "out" /\ ProcessEnabled(self)
             /\ pi_locks' = [pi_locks EXCEPT ![(work[self].p)] = NULL]
             /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] - 1]
             /\ IF self \in SCHED_TASKS /\ preempt_count'[self] = 0
                   THEN /\ \E tsk \in         {t \in runqueues[(CHOOSE cpu \in CPUS : currents[cpu] = self)] : \A other \in runqueues[(CHOOSE cpu \in CPUS : currents[cpu] = self)] \ {t} :
                                      task_structs[t].prio >= task_structs[other].prio}:
                             currents' = [currents EXCEPT ![(CHOOSE cpu \in CPUS : currents[cpu] = self)] = tsk]
                   ELSE /\ TRUE
                        /\ UNCHANGED currents
             /\ pc' = [pc EXCEPT ![self] = "st9"]
             /\ UNCHANGED << task_structs, task_cpu, runqueues, my_pending, 
                             stopper_wait, stopper_work, stack, p_, dest_cpu, 
                             p, mask, enable_migration, pending_ref, complete, 
                             rq_cpu, dest_cpu_, do_complete, work, p_pending >>

st9(self) == /\ pc[self] = "st9" /\ ProcessEnabled(self)
             /\ IF do_complete[self]
                   THEN /\ my_pending' = [my_pending EXCEPT ![p_pending[self]].completed = TRUE]
                   ELSE /\ TRUE
                        /\ UNCHANGED my_pending
             /\ pc' = [pc EXCEPT ![self] = "dec"]
             /\ UNCHANGED << task_structs, preempt_count, task_cpu, runqueues, 
                             currents, stopper_wait, pi_locks, stopper_work, 
                             stack, p_, dest_cpu, p, mask, enable_migration, 
                             pending_ref, complete, rq_cpu, dest_cpu_, 
                             do_complete, work, p_pending >>

dec(self) == /\ pc[self] = "dec" /\ ProcessEnabled(self)
             /\ IF work[self].pending # NULL
                   THEN /\ my_pending' = [my_pending EXCEPT ![work[self].pending].refcount = my_pending[work[self].pending].refcount - 1]
                   ELSE /\ TRUE
                        /\ UNCHANGED my_pending
             /\ pc' = [pc EXCEPT ![self] = "comp"]
             /\ UNCHANGED << task_structs, preempt_count, task_cpu, runqueues, 
                             currents, stopper_wait, pi_locks, stopper_work, 
                             stack, p_, dest_cpu, p, mask, enable_migration, 
                             pending_ref, complete, rq_cpu, dest_cpu_, 
                             do_complete, work, p_pending >>

comp(self) == /\ pc[self] = "comp" /\ ProcessEnabled(self)
              /\ IF work[self].wait # NULL
                    THEN /\ stopper_wait' = [stopper_wait EXCEPT ![work[self].wait] = TRUE]
                    ELSE /\ TRUE
                         /\ UNCHANGED stopper_wait
              /\ pc' = [pc EXCEPT ![self] = "st0"]
              /\ UNCHANGED << task_structs, preempt_count, task_cpu, runqueues, 
                              currents, my_pending, pi_locks, stopper_work, 
                              stack, p_, dest_cpu, p, mask, enable_migration, 
                              pending_ref, complete, rq_cpu, dest_cpu_, 
                              do_complete, work, p_pending >>

stop(self) == st0(self) \/ st1(self) \/ st2(self) \/ lock(self)
                 \/ st3(self) \/ st4(self) \/ st5(self) \/ any(self)
                 \/ st6(self) \/ st77(self) \/ st7(self) \/ st8(self)
                 \/ out(self) \/ st9(self) \/ dec(self) \/ comp(self)

pr0(self) == /\ pc[self] = "pr0" /\ ProcessEnabled(self)
             /\ \/ /\ runqueues' = [runqueues EXCEPT ![task_cpu[self]] = runqueues[task_cpu[self]] \ {self}]
                   /\ \E tsk \in         {t \in runqueues'[(CHOOSE cpu \in CPUS : currents[cpu] = self)] : \A other \in runqueues'[(CHOOSE cpu \in CPUS : currents[cpu] = self)] \ {t} :
                                 task_structs[t].prio >= task_structs[other].prio}:
                        currents' = [currents EXCEPT ![(CHOOSE cpu \in CPUS : currents[cpu] = self)] = tsk]
                \/ /\ TRUE
                   /\ UNCHANGED <<runqueues, currents>>
             /\ pc' = [pc EXCEPT ![self] = "pr0"]
             /\ UNCHANGED << task_structs, preempt_count, task_cpu, my_pending, 
                             stopper_wait, pi_locks, stopper_work, stack, p_, 
                             dest_cpu, p, mask, enable_migration, pending_ref, 
                             complete, rq_cpu, dest_cpu_, do_complete, work, 
                             p_pending >>

hpio(self) == pr0(self)

t0(self) == /\ pc[self] = "t0" /\ ProcessEnabled(self)
            /\ \/ /\ TRUE
                  /\ pc' = [pc EXCEPT ![self] = "t1"]
                  /\ UNCHANGED <<task_cpu, runqueues, stack, p_, dest_cpu>>
               \/ /\ Assert(~task_structs[(PCPU_TASK(HPRIO_TASK, self[2]))].migration_disabled, 
                            "Failure of assertion at line 191, column 9 of macro called at line 561, column 25.")
                  /\ \E cpu \in task_structs[(PCPU_TASK(HPRIO_TASK, self[2]))].cpus_mask:
                       /\ task_cpu' = [task_cpu EXCEPT ![(PCPU_TASK(HPRIO_TASK, self[2]))] = cpu]
                       /\ runqueues' = [runqueues EXCEPT ![cpu] = runqueues[cpu] \union {(PCPU_TASK(HPRIO_TASK, self[2]))}]
                  /\ pc' = [pc EXCEPT ![self] = "t1"]
                  /\ UNCHANGED <<stack, p_, dest_cpu>>
               \/ /\ /\ dest_cpu' = [dest_cpu EXCEPT ![self] = self[2]]
                     /\ p_' = [p_ EXCEPT ![self] = MD_TASK]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "migrate_task",
                                                              pc        |->  "t1",
                                                              p_        |->  p_[self],
                                                              dest_cpu  |->  dest_cpu[self] ] >>
                                                          \o stack[self]]
                  /\ pc' = [pc EXCEPT ![self] = "mt0"]
                  /\ UNCHANGED <<task_cpu, runqueues>>
            /\ UNCHANGED << task_structs, preempt_count, currents, my_pending, 
                            stopper_wait, pi_locks, stopper_work, p, mask, 
                            enable_migration, pending_ref, complete, rq_cpu, 
                            dest_cpu_, do_complete, work, p_pending >>

t1(self) == /\ pc[self] = "t1" /\ ProcessEnabled(self)
            /\ IF preempt_count[currents[self[2]]] = 0
                  THEN /\ \E tsk \in         {t \in runqueues[(self[2])] : \A other \in runqueues[(self[2])] \ {t} :
                                     task_structs[t].prio >= task_structs[other].prio}:
                            currents' = [currents EXCEPT ![(self[2])] = tsk]
                  ELSE /\ TRUE
                       /\ UNCHANGED currents
            /\ pc' = [pc EXCEPT ![self] = "t0"]
            /\ UNCHANGED << task_structs, preempt_count, task_cpu, runqueues, 
                            my_pending, stopper_wait, pi_locks, stopper_work, 
                            stack, p_, dest_cpu, p, mask, enable_migration, 
                            pending_ref, complete, rq_cpu, dest_cpu_, 
                            do_complete, work, p_pending >>

tick(self) == t0(self) \/ t1(self)

Next == (\E self \in ProcSet:  \/ migrate_task(self)
                               \/ set_cpus_allowed_ptr(self)
                               \/ migrate_disable(self)
                               \/ migrate_enable(self))
           \/ (\E self \in {MD_TASK}: md(self))
           \/ (\E self \in AFFINER_TASKS: aff(self))
           \/ (\E self \in STOPPER_TASKS: stop(self))
           \/ (\E self \in HPRIO_TASKS: hpio(self))
           \/ (\E self \in TICK_TASKS: tick(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {MD_TASK} : /\ WF_vars(md(self))
                                   /\ WF_vars(migrate_disable(self))
                                   /\ WF_vars(migrate_enable(self))
                                   /\ WF_vars(set_cpus_allowed_ptr(self))
        /\ \A self \in AFFINER_TASKS : WF_vars(aff(self)) /\ WF_vars(set_cpus_allowed_ptr(self))
        /\ \A self \in STOPPER_TASKS : WF_vars(stop(self))
        /\ \A self \in HPRIO_TASKS : WF_vars(hpio(self))
        /\ \A self \in TICK_TASKS : WF_vars(tick(self)) /\ WF_vars(migrate_task(self))

\* END TRANSLATION

PendingCompletionOK ==
	\A tsk \in AFFINER_TASKS:
		(* tsk is awaiting on pending completion *)
		/\ pc[tsk] = "sca14"
		(* It installed a pending *)
		/\ task_structs[MD_TASK].pending_ref = tsk
		/\ ~task_structs[MD_TASK].migration_disabled
		(*
		* Then either some affinity-tweaking thread or some stopper
		* thread must be able to make fwd progress.
		*)
		=> \/ \E aff_tsk \in AFFINER_TASKS :
		    \/ ENABLED(aff(aff_tsk))
		    \/ ENABLED(set_cpus_allowed_ptr(aff_tsk))
		  \/ \E cpu \in CPUS: runqueues[cpu] \cap STOPPER_TASKS # {}

=====
