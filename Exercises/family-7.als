module family
open util/ordering [Time] as T

---------------- Signatures ----------------

sig Time {}

abstract sig Person {
  -- primitive relations
	children: Person set -> Time,
	spouse: Person lone -> Time,
	alive: set Time,
} 

sig Man, Woman extends Person {}

abstract sig Operator {}
one sig Dies, IsBornFromParents, GetMarried extends Operator {}

one sig Track { 
  op: Operator lone -> Time
}

--------------
-- Predicates
--------------


---------------------
-- Derived relations
---------------------

-- These derived relations are defined here as macros, to keep the model lean

fun parents [t: Time]: Person -> Person {
  ~(children.t)
}

fun siblings [p: Person, t: Time]: Person {
  { q : Person - p | some q.(parents[t]) and p.(parents[t]) = q.(parents[t]) }
}

-- Two persons are blood relatives at time t iff 
-- they have a common ancestor at time t
-- (alternative definition in based directly on children)
pred BloodRelatives [p: Person, q: Person, t: Time, ]  {
  some a: Person | p+q in a.*(children.t)	
}


------------------------------
-- Frame condition predicates
------------------------------

pred noChildrenChangeExcept [ps: set Person, t,t': Time, ] {
	  all p: Person - ps | p.children.t' = p.children.t
}

pred noSpouseChangeExcept [ps: set Person, t,t': Time] {
	  all p: Person - ps | p.spouse.t' = p.spouse.t
}

pred noAliveChange [t, t': Time] {
	  alive.t' = alive.t
}


-------------
-- Operators
-------------

pred getMarried [p,q: Person, t,t': Time] {
	-- Pre-condition
     -- p and q must be alive before marriage (at time t)
	   p+q in alive.t
	   -- they must not be married
     no (p+q).spouse.t
     -- they must not be blood relatives
     not BloodRelatives [p, q, t]
	-- Post-condition
	   -- After marriage they are each other's spouses
     q in p.spouse.t'
     p in q.spouse.t'
	-- Frame condition
     noChildrenChangeExcept [none, t, t']
     noSpouseChangeExcept [p+q, t, t']
     noAliveChange [t, t']

     Track.op.t' = GetMarried
}

pred isBornFromParents [p: Person, m: Man, w: Woman, t,t': Time] {
	-- Pre-condition
     m+w in alive.t
     p !in alive.t
	-- Post-condition and frame condition
     alive.t' = alive.t + p
     m.children.t' = m.children.t + p
     w.children.t' = w.children.t + p
	-- Frame condition
     noChildrenChangeExcept [m+w, t, t']
     noSpouseChangeExcept [none, t, t']

     Track.op.t' = IsBornFromParents
}

pred dies [p: Person, t,t': Time] {
	-- Pre-condition
     p in alive.t
	-- Post-condition
     no p.spouse.t'
     
  -- Post-condition and frame condition
     alive.t' = alive.t - p
     all s: p.spouse.t | s.spouse.t' = s.spouse.t - p

	-- Frame condition
     noChildrenChangeExcept [none, t, t']
     noSpouseChangeExcept [p + p.spouse.t, t, t']

     Track.op.t' = Dies
}


---------------------------
-- Inital state conditions
---------------------------
pred init [t: Time] {
	no children.t
  no spouse.t
	#alive.t > 2
  #Person > #alive.t
}

-----------------------
-- Transition relation
-----------------------
pred trans [t,t': Time]  {
  (some p,q: Person | getMarried [p, q, t, t'])
  or 
  (some p: Person, m: Man, w: Woman | isBornFromParents [p, m, w, t, t'])
  or 
  (some p :Person | dies [p, t, t'])
}

-------------------
-- System predicate
-------------------
-- Denotes all possible executions of the system from a state
-- that satisfies the init condition
pred System {
	init [T/first]
  all t: Time - T/last | trans [t, T/next[t]]
}

---------------------------
-- Sanity-check predicates
---------------------------

pred sc1 [] {
  -- having children is possible
  some t: Time | some children.t
}

pred sc2 [] {
  -- births can happen
  some t: Time | some p: Person | p in alive.t and p !in alive.(T/next[t])
}

pred sc3 [] {
  -- people can get married
  some t: Time | some p: Person | some q: Person - p | q in p.spouse.t
}


run {
 #Man > 1
 #Woman > 1
 System
 -- uncomment any of sanity-check predicates to check it
  -- sc1
  -- sc2
  -- sc3
}  for 10 but 8 Time 



-- Only living people can have children
assert a1 {
  System => all t: Time | all p: Person |
             (some p.children.t) => p in alive.t
}

check a1 for 10 but 6 Time 

-- Only people that are or have been alive can have children
assert a2 {
  System => all t: Time | all p: Person |
             (some p.children.t) => some t': t+t.prevs | p in alive.t'
}

check a2 for 10 but 6 Time 

-- Only living people can be married
assert a3 {
  System => all t: Time | all p: Person |
             (some p.spouse.t) => p in alive.t
}
check a3 for 10 but 6 Time 

-- No person can be their own ancestor
assert a4 {
  System => all t: Time | no p: Person | p in p.^(parents[t])
}
check a4 for 10 but 6 Time 

-- No person can have more than one father or mother
assert a5 {
  System => all t: Time | all p: Person | 
             lone (p.(parents[t]) & Man) and 
             lone (p.(parents[t]) & Woman)
}
check a5 for 10 but 6 Time 

-- Each married woman has a husband
assert a6 {
  System => all t: Time | all w: Woman | some (w.spouse.t & Man)
}
check a6 for 10 but 6 Time 

-- A spouse can't be a sibling
assert a7 {
  System => all t: Time | all p: Person | all q: p.spouse.t |
             q !in siblings[p, t]
}
check a7 for 10 but 6 Time 

 -- the spouse relation is symmetric
assert a8 {
  System => all t: Time | spouse.t = ~(spouse.t)
}
check a8 for 10 but 4 Time 

