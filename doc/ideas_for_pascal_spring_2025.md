# Overview

Let's look at the complexity of FOND HTN planning.
Let me sum up the state of the art as far as I know, and I insert my beliefs in square brackets.

## Your 2021 paper with Dilon Chen:

This paper was about solutions with fixed decomposition methods.

Looking at Table 1 you solved all but three questions (discarding the one about polynomial time, as I have no background knowledge on P-completeness).
For strong outcome-dependent solutions and partial order:
- acyclic: only EXPSPACE membership given [I believe this is tight -- see counters below]
- regular: only EXPSPACE membership given, and Gregor and I show hardness in our paper "Hardness of Chosen ..." accepted at ICAPS 2025
- tail-recursive: only semidecidability given [I believe it is undecidable -- see PCP below]

## Your 2022 paper with Dilon Chen:

This paper was about solutions with flexible decomposition methods.

Looking at Table 1 you solved all but three questions (again discarding the ones about polynomial time).
- strong cyclic plans for partial order tail-recursive: only 2-EXPTIME membership given [I believe this is tight -- see counters below]
- strong or strong cyclic plans for total order (arbitrary hierarchy): only semidecidability given [I believe they are 2-EXPTIME-complete -- see total order below]

# Proof ideas

I do not have full proofs, but I will try to explain my thoughts.

## PCP

Reducing the Post Correspondence Problem to a tail-recursive fixed methods problem.
Consider an initial task network with two unordered compound tasks and one primitive task ordered before the two compound tasks.
Each compound task corresponds to one of the two sets of words in the PCP.
The compound tasks are decomposed in a regular fashion, with a method for each word in the PCP.
The initializer task has two non-deterministic possible outcomes: it activates "character mode" or "word mode".
If we are in character mode, we check that the characters of the words into which we decomposed the two compound tasks match up.
If we are in word mode, we check that we decomposed the two compound tasks into words with the same indices.

## Counters

Theorem 6.1 of your 2015 paper "Tight Bounds for HTN Planning" with Alford and Aha translates a Turing machine into HTN using counters.
Gregor explained the ideas to me. I found it remarkable and tried to visualize what is going on.
My impression is that this proof can also be done with fewer methods.
My vision of the proof is as follows.
We want to model a Turing machine with 2^n tape cells.
Assume there are only two symbols (0 and 1) and the tape initially contains only 0's.
Further, assume the machine has goal states but no halting states -- the machine runs forever and the question is whether there exists a moment in time when the machine is in a goal state.
We take a disjoint union of one control network, many "0-cells" and many "1-cells". (I will describe these task networks and how many below.)
There are three levels of time.
Every time step of the Turing machine is subdivided into 2^n smaller time steps; call them atomic time steps.
Every atomic time step is again subdivided into 2^n even smaller time steps; call them subatomic time steps.
Every cell task network has a clock running until 2^n at atomic speed, so it is executed over the course of a global time step.
A cell needs to be "initialized" before its clock can be incremented.
After a cell is initialized, or its clock incremented, it is automatically paused. It has to be resumed before it can be incremented again. And it can only be resumed if it is on pause.
The control task network has two clocks, each running until 2^n, but one at atomic speed and the other at subatomic speed.
All clocks can be encoded in HTN using acyclic methods and propositional variables (e.g. a variable INCREMENT saying that control is waiting for any clock to be incremented).
The internal state and the head position of the Turing machine can be directly encoded in propositional variables.
Control first initializes the tape as follows:
for atomic clock in [0,2^n):
	for subatomic clock in [0, atomic clock):
		increment the clock of some cell that has already been initialized
	for subatomic clock in [0, atomic clock):
		resume some cell
	initialize a 0-cell (with clock at 0)
(Splitting the increment and the resume into two loops makes sure that we don't increment the same clock twice in one iteration of the outer loop.)
Then control lets the machine run as follows (each iteration of the main loop is a global time step):
head := 0
internal state := initial state
while true:
	for atomic clock in [0,2^n):
		find the unique memory cell C whose clock is at 2^n-1
		find sigma in {0,1} such that C is a sigma-cell
		finalize C
		if atomic clock == head:
			based on the read symbol sigma and the specifics of the Turing machine, let sigma' be the new symbol to be written and update head and internal state
			initialize a new sigma'-cell
		else:
			initialize a new sigma-cell
		for subatomic clock in [1,2^n):
			increment some memory cell's clock
		for subatomic clock in [0,2^n):
			resume some memory cell
For 2^n global time steps, it suffices to generate 2^(2n) 0-cells and 2^(2n) 1-cells, and all of this can be encoded into HTN using only one method for every compound task name. (Often times, when a natural encoding involves multiple methods for a single compound task name, it is possible to do it with only one using a "backup and trash" mechanism (cf. our papers "Barely Dedicable Fragments of Planning" and "Hardness of Chosen ..."): combine all method task networks into one: first execute one of them, then backup relevant propositional variables, then execute the rest, and finally restore the backup.)
For unlimited time steps, we can make a tail-recursive problem such that three compound task names (one for control, one for 0-cells, and one for 1-cells) have two methods each ("stop" and "continue") and all other compound task names have only one method. The choice of method ("stop" or "continue") concerns whether or not you want to add more global time (a new memory cell, a new atomic clock, and 2^n new subatomic clocks in the case of control). For every application of "continue" in control there should be (at least) 2^n applications of "continue" for cells. We want a tail-recursive problem so some of the cells will be ordered after each other, but that seems fine as we never need more than 2^n 0- or 1-cells at the same time.
We do the encoding in such a way that a plan need not end exactly with one of the machine's goal states -- instead, when a goal state is reached, we set some propositional flag to true that allows the HTN to execute all tasks (via "cheat"-tasks that require this flag and have all sorts of effects).
With deterministic HTNs, you get the following hardness results (Theorem 6.1 of the 2015 paper):
- acyclic (2^n global time steps): NEXPTIME
- tail-recursive (unlimited global time steps): EXPSPACE
With non-determinism we can encode an alternating machine, so we get:
- acyclic: AEXPTIME=EXPSPACE (for flexible methods this is Theorem 4.5 from the 2022 paper)
- tail-recursive: AEXPSPACE=2-EXPTIME
I believe this works for all three solution concepts (fixed methods, flexible methods strong, flexible methods strong cyclic): in the acyclic case there is only one choice of methods, and in the tail-recursive case the only choice of methods amounts to the number of global time steps and it can never hurt to add more global time steps.
(For strong cyclic plans for a tail-recursive problem, we set the HTN objective to *not* reach a goal state of the Turing machine, and the planner should keep adding global time steps forever.)

## Total order

### Membership

Let's start with strong plans.

I want to make a big table T of triples consisting of a compound task name, a propositional state, and a set of propositional states.
(c, s, S') in T means that a compound task with name c can be executed in propositional state s ending in some state in S', in the sense that the planner (with flexible methods) can make sure to end in a state in S' after completing c, regardless of non-determinism.

P := {propositional variables}
T := empty set
while T is growing:
	for each compound task name c:
		for s subseteq P:
			for S' subseteq pow(P):
				for each method mu for c:
					let tau be the task network of mu
					let n be the number of compound tasks in tau
					for each n-tuple (f_1, ..., f_n) of partial functions f_i: pow(P) -> pow(pow(P)) \ {{}}: (*)
						for i = 1, ..., n:
							for s' in domain(f_i):
								if (ith compound task in tau', s', f_i(s')) not in T:
									continue with the loop (*)
						tau' := tau
						for i = 1, ..., n:
							replace the ith compound task of tau' by an artificial primitive task that has the effect of changing a propositional state s' into some propositional state in f_i(s') (precondition is that s' in domain(f_i); an state in f_i(s') is chosen by non-determinism)
						generate the full state tree of executing tau' starting in state s -- if a precondition is violated anywhere in the tree, immediately continue with the loop (*)
						if the set of leaf states of the tree is exactly S':
							add the triple (c, s, S') to T
s_0 := initial propositional state
c_0 := compound task in the initial task network (w.l.o.g. the initial task network has only one task)
return (there exists a nonempty S' such that (c_0, s_0, S') in T)

Notice that n can be zero.

For strong cyclic plans, I suggest to approach the fixpoint T from the other side.
Initialize T as the set of all triples.
(c, s, S') in T means that (we have not yet refuted that) compound task c can be commenced in propositional state s either ending in some state in S' or never finishing.
Concretely, in the above algorithm, instead of adding (c, s, S') to T we continue with the next S'; if we complete the loop over methods mu for c, we remove (c, s, S') from T.
This is not exactly correct yet: we should be more careful about the case S'={}. A triple (c, s, {}) is now sensible, meaning that (we have not yet refuted that) compound task c can be commenced in state s without ever finishing (regardless of non-determinism).

### Hardness

We model a Turing machine with a run of length 2^2^n in a totally ordered problem.
The totally ordered problem has only a linear number of propositional variables, so it will be a sort of paradox if this works.
I got this idea by looking at the membership algorithm and thinking of some fixed c, s; calculating the next timestep of the machine will correspond to adding a new triple of the form (c, s, S') to T. This c is called <advance> below.
Let q_0 be the machine's initial internal state.
Assume the machine has only one halting state q_h.
Propositional variables:
CHECK_i for i = 0, ..., n-1
CHOICE_i for i = 0, ..., n-1
SYMBOL_sigma for each symbol sigma in the machine's alphabet
INTSTATE_q for each internal state q of the machine
TIME
TIMEVERIFY
HEAD
HEADVERIFY
HEADNEW
TAPE
TAPEVERIFY
MACHMODE
TAPEMODE
Initial state: {INTSTATE_(q_0)}
Initial task network: <advance>; [assert INTSTATE_(q_h)]
(I write compound tasks in <> and primitive tasks in [].)
Let Check < 2^n be the number encoded by the variables CHECK_i: Check = 1 * CHECK_0 + ... + 2^(n-1) * CHECK_(n-1).
The following are the central claims of the proof:
'''Tape''': cell C < 2^2^n contains symbol sigma at time t < 2^2^n iff, starting in the initial propositional state, we can execute <advance> guaranteeing that afterwards:
  * SYMBOL_sigma holds
  * TAPE holds iff the Check-th digit of C is 1
  * TIME holds iff the Check-th digit of t is 1
'''Machine''': the internal state is q and the head is at position C < 2^2^n at time t < 2^2^n iff, starting in the initial propositional state, we can execute <advance> guaranteeing that afterwards:
  * INTSTATE_q holds
  * HEAD holds iff the Check-th digit of C is 1
  * TIME holds iff the Check-th digit of t is 1
Here "execute" means provide a branching plan containing method applications and primitive task executions such that all the leaf nodes satisfy the `*' conditions stated afterwards.
Methods.
In the above claims '''Tape''' and '''Machine''', the planner wants to "prove" something about the run of the machine (the content of a certain tape cell, the position of the head, or the internal state at some point in time).
If t>0, the planner has two ways of doing this: looking at the location of the head at time t-1 and applying the transition of the Turing machine ("transition", useful for both claims), or looking at any other location on the tape and say that the tape content at time t is the same as at time t-1 ("preserve", useful only for '''Tape''').
The planner chooses either of the two by means of a method application, and then applies methods for <transition> resp. <preserve> to encode the time t (corresponding to TIME) and the location C (corresponding to TAPE) into the task network. In the case of <preserve> the planner also encodes the location of the head (corresponding to HEAD) and we demand that this differs from C. "Transition" proves something about the tape content not at the location of the head but next to it (as the head moved).
Encoding such a number < 2^2^n (e.g. t) into the task network is done by having the variables CHOICE_i run through all numbers d < 2^n and including <addmaybe(..)> (e.g. <addmaybe(TIME)>) if digit d (of e.g. t) is 1 and <delmaybe(..)> if digit d is 0.
After the planner has made all required decisions for timestep t, non-determinism feeds back either TAPEMODE or MACHMODE asking the planner to recursively prove '''Tape''' resp. '''Machine''' for t-1.
Below, "perhaps" refers to non-determinism; positive and negative preconditions are described with the keywords "assert" and "forbid". V and W stand for propositional variables.
("carryover" informally refers to the addition algorithm (for numbers < 2^2^n).)
<addmaybe(V)>: <asserteq(CHOICE_0,CHECK_0)>; ...; <asserteq(CHOICE_(n-1),CHECK_(n-1)>; [add V]
<addmaybe(V)>: [assert CHOICE_i]; [forbid CHECK_i]
<addmaybe(V)>: [forbid CHOICE_i]; [assert CHECK_i]
(for all i)
<advance>: [perhaps add CHECK_0]; ...; [perhaps add CHECK_(n-1)]; <choose(TAPE)>
<advance>: <preserve>; <addmaybe(TAPEVERIFY)>; <delmaybe(HEADVERIFY)>; <preserveverify>; <get(sigma)>; <let(sigma)>; [perhaps add HEAD]; [perhaps del HEAD]; [del INTSTATE_q for each internal state q]; <copy(TAPEVERIFY,TAPE)>
(for all sigma)
<advance>: <preserve>; <delmaybe(TAPEVERIFY)>; <addmaybe(HEADVERIFY)>; <preserveverify>; <get(sigma)>; <let(sigma)>; [perhaps add HEAD]; [perhaps del HEAD]; [del INTSTATE_q for each internal state q]; <copy(TAPEVERIFY,TAPE)>
(for all sigma)
<advance>: <transitionright>; <transitionverify(sigma,q)>; <get(sigma)>; <let(sigma')>; <goto(q')>; <copy(HEADNEW,HEAD)>; <copy(TAPEVERIFY,TAPE)>
(for all sigma, sigma', q, and q' such that the machine, when reading symbol sigma in state q, writes symbol sigma', transitions to state q', and moves the head to the right)
<advance>: <transitionleft>;  <transitionverify(sigma,q)>; <get(sigma)>; <let(sigma')>; <goto(q')>; <copy(HEADNEW,HEAD)>; <copy(TAPEVERIFY,TAPE)>
(for all sigma, sigma', q, and q' such that the machine, when reading symbol sigma in state q, writes symbol sigma', transitions to state q', and moves the head to the left)
<advanceandclock>: <advanceandcarryover>; <forbidmaybe(TIME)>; <addmaybe(TIME)>; [del TIMEVERIFY]; [del HEADVERIFY]; [del TAPEVERIFY]; [del CHOICE_0]; ...; [del CHOICE_(n-1)]
<advanceandcarryover>: <advanceandcarryover>; <assertmaybe(TIME)>; <delmaybe(TIME)>; <inc>
<advanceandcarryover>: [add MACHMODE and del TAPEMODE]; [perhaps (del MACHMODE and add TAPEMODE)]; <advanceinmode>; [del CHOICE_0]; ...; [del CHOICE_(n-1)]
<advanceinmode>: [assert MACHMODE]; <advance>; [del TAPEMODE]; [add MACHMODE]
<advanceinmode>: [assert TAPEMODE]; <advance>; [del MACHMODE]; [add TAPEMODE]
<asserteq(V,W)>: [assert V and W]
<asserteq(V,W)>: [forbid V and W]
<choose(V)>: [add V]
<choose(V)>: [del V]
<copy(V,W)>: [assert V]; [add W]
<copy(V,W)>: [forbid V]; [del W]
<delmaybe(V)>: <asserteq(CHOICE_0,CHECK_0)>; ...; <asserteq(CHOICE_(n-1),CHECK_(n-1)>; [del V]
<delmaybe(V)>: [assert CHOICE_i]; [forbid CHECK_i]
<delmaybe(V)>: [forbid CHOICE_i]; [assert CHECK_i]
(for all i)
<get(sigma)>: [assert TAPEMODE]; [assert SYMBOL_sigma]
<get(sigma)>: [forbid TAPEMODE]
<goto(q)>: [del INTSTATE_q' for each internal state q']; [add INTSTATE_q]
<inc>: [assert CHOICE_0]; ...; [assert CHOICE_(i-1)]; [forbid CHOICE_i]; [del CHOICE_0]; ...; [del CHOICE_(i-1)]; [add CHOICE_i]
(for all i)
<let(sigma)>: [del SYMBOL_sigma' for each symbol sigma']; [add SYMBOL_sigma]
<preserve>: <advanceandclock>
<preserve>: <preserve>; <inc>
<preserve>: <preserve>; <addmaybe(TAPEVERIFY)>
<preserve>: <preserve>; <delmaybe(TAPEVERIFY)>
<preserve>: <preserve>; <addmaybe(HEADVERIFY)>
<preserve>: <preserve>; <delmaybe(HEADVERIFY)>
<preserve>: <preserve>; <addmaybe(TIMEVERIFY)>
<preserve>: <preserve>; <delmaybe(TIMEVERIFY)>
<preserveverify>: [assert TAPEMODE]; <asserteq(TAPE,TAPEVERIFY)>; <asserteq(TIME,TIMEVERIFY)>
<preserveverify>: [assert MACHMODE]; <asserteq(HEAD,HEADVERIFY)>; <asserteq(TIME,TIMEVERIFY)>
<transition>: <advanceandclock>
<transition>: <transition>; <inc>
<transition>: <transition>; <addmaybe(TAPEVERIFY)>
<transition>: <transition>; <delmaybe(TAPEVERIFY)>
<transition>: <transition>; <addmaybe(TIMEVERIFY)>
<transition>: <transition>; <delmaybe(TIMEVERIFY)>
<transitionleft>:  <transitionandcarryoverleft>;  <assertmaybe(HEADNEW)>; <delmaybe(HEADNEW)>
<transitionright>: <transitionandcarryoverright>; <forbidmaybe(HEADNEW)>; <addmaybe(HEADNEW)>
<transitionandcarryoverleft>:  <transitionandcarryoverleft>;  <forbidmaybe(HEADNEW)>; <addmaybe(HEADNEW)>; <inc>
<transitionandcarryoverleft>:  <transition>; [del CHOICE_0]; ...; [del CHOICE_(n-1)]; <copy(TAPEVERIFY,HEADNEW)>
<transitionandcarryoverright>: <transitionandcarryoverright>; <assertmaybe(HEADNEW)>; <delmaybe(HEADNEW)>; <inc>
<transitionandcarryoverright>: <transition>; [del CHOICE_0]; ...; [del CHOICE_(n-1)]; <copy(TAPEVERIFY,HEADNEW)>
<transitionverify(sigma,q)>: [assert TAPEMODE]; <asserteq(TAPE,TAPEVERIFY)>; <asserteq(TIME,TIMEVERIFY)>; [assert SYMBOL_sigma]
<transitionverify(sigma,q)>: [assert MACHMODE]; <asserteq(HEAD,TAPEVERIFY)>; <asserteq(TIME,TIMEVERIFY)>; [assert INTSTATE_q]
In the "preserve" methods for <advance>, the tasks <addmaybe(TAPEVERIFY)> and <delmaybe(HEADVERIFY)> (or vice versa) are there to make sure that the planner encodes two different numbers, differing at the digit stored in the CHOICE_i variables.
Notice that CHECK_i are never deleted.
Notice that only TAPEMODE and MACHMODE are effected by non-determinism before a recursive compound task. This means that the partial witness of the Turing machine run that the planner provides is only based on whether a proof for the tape or a proof for the machine is demanded at each time step.
It is easy to check that the central claims '''Tape''' and '''Machine''' hold for t=0 using the first method for <advance>.
For the inductive step we have to distinguish cases...
