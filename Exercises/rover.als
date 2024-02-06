--===============================================
-- CS:5810 Formal Methods in Software Engineering
-- Fall 2017
--
-- Cesare Tinelli
--===============================================


/*
This Alloy model models a dynamic domain involving several rovers 
moving on in a two-dimentional space.

The model is based on the following facts about this domain.

- There are one or more identical rovers.
- Each rover can only move forward, or turn in place to the left or 
  to the right. 
- Each rover can be turned on and off.

We make the following simplifying modeling choices:

1) We adopt an interleaving model of time, where only one action is performed, 
by one of the rovers, at a time.

2) The two dimentional space is a discrete grid, with the X-coordinate 
growing indefinitely in the West-East direction and the Y-coordinate 
growing indefinitely in the South-North direction (see picture below). 

3) Rovers move only by one position at a time and along the X,Y axes.

4) As a consequence of (2) and (3), a rover turns left or right by exactly
   90 degrees. 

4) A rover can move only in the direction it is facing.



-----------------------------------------------------------------------
y

.    .   .   .   .   .  
.    .   .   .   .   .  
.    .   .   .   .   .   
c4 |   |   |   |   |   | ...
   ---------------------
c3 |   |   |   |   |   | ...
   ---------------------
c2 |   |   |   |   |   | ...
   ---------------------
c1 |   |   |   |   |   | ...
   ---------------------
c0 |   |   |   |   |   | ...
   ---------------------
    c0  c1  c2  c3  c4  ...  x

*/

open util/ordering [Time] as T
open util/ordering [Coor] as C

sig Time {}

-- Coordinates, strictly ordered
sig Coor {} 

-- Position models the individual positions in the grid
sig Position {
  x: Coor,
  y: Coor
}

-- The four cardinal directions
abstract sig Direction {}
one sig North, South, East, West extends Direction {}


some sig Rover {
  -- direction rover is facing at any one time
  dir: Direction one -> Time,

  -- rover's position at any one time
  pos: Position one -> Time,

  -- rover's on/off status and any one time
  on: set Time
}


-------------
-- Operators
-------------

pred turn_on [rov: Rover, t,t': Time] {
-- preconditions  
   -- rover is off
   !is_on[rov, t] 
-- postconditions  
   -- rover is on
   is_on[rov, t']
-- frame conditions
   -- all other rovers stay on or off as they were
   no_on_changes[Rover - rov, t, t']
  -- No rover changes direction  
   no_direction_changes[Rover, t, t']
   -- No rover changes position
   no_position_changes[Rover, t, t']
}

pred turn_off [rov: Rover, t,t': Time] {
-- preconditions  
   -- rover is on
   is_on[rov, t]
-- postconditions  
   -- rover is off
   !is_on[rov, t']
-- frame conditions
   -- all other rovers stay on or off as they were
   no_on_changes[Rover - rov, t, t']
  -- No rover changes direction  
   no_direction_changes[Rover, t, t']
   -- No rover changes position
   no_position_changes[Rover, t, t']
}

pred turn_left [rov: Rover, t,t': Time] {
-- preconditions  
   -- rover is on
   is_on[rov, t]
-- postconditions
   -- direction changes
   let d = rov.dir.t |
   let d' = ((d = North) => West else
             (d = West)  => South else
             (d = South) => East else
                            North
            ) |
     rov.dir.t' = d'
-- frame conditions
   -- all rovers stay on or off as they were
   no_on_changes[Rover, t, t']
  -- No other rover changes direction  
   no_direction_changes[Rover - rov, t, t']
   -- No rover changes position
   no_position_changes[Rover, t, t']
}

pred turn_right [rov: Rover, t,t': Time] {
-- preconditions  
   -- rover is on
   is_on[rov, t]
-- postconditions
   -- direction changes
   let d = rov.dir.t |
   let d' = ((d = North) => East else
             (d = West)  => North else
             (d = South) => West else
                            South
            ) |
     rov.dir.t' = d' 
-- frame conditions
   -- all rovers stay on or off as they were
   no_on_changes[Rover, t, t']
  -- No other rover changes direction  
   no_direction_changes[Rover - rov, t, t']
   -- No rover changes position
   no_position_changes[Rover, t, t']
}

pred go [rov: Rover, d: Direction, t,t': Time] {
-- preconditions  
   -- rover is on
   is_on[rov, t]
   -- d is rover's direction
   rov.dir.t = d
   let np = next_pos[rov.pos.t, d] | {
     -- precondition
     some np
     --postcondition
     rov.pos.t' = np
   }
-- frame conditions
   -- all rovers stay on or off as they were
   no_on_changes[Rover, t, t']
  -- No rover changes direction  
   no_direction_changes[Rover, t, t']
   -- No other rover changes position
   no_position_changes[Rover - rov, t, t']
}

--------------------------------------
-- Auxiliary predicates and functions
--------------------------------------

-- holds iff r is on at time t
pred is_on [r: Rover, t: Time] {
  t in r.on
}

-- holds iff the on/off status of the rovers in R does not change
pred no_on_changes [R: set Rover, t,t': Time] {
  all r: R |
    t' in r.on iff t in r.on 
}

--  holds iff the position of the rovers in R does not change
pred no_position_changes [R: set Rover, t,t': Time] {
  all r: R |
    r.pos.t' = r.pos.t 
}

-- holds iff the direction of the rovers in R does not change
pred no_direction_changes [R: set Rover, t,t': Time] {
  all r: R |
    r.dir.t' = r.dir.t 
}

-- returns the position next to p along direction d, if any,
-- and the empty set otherwise
fun next_pos [p: Position, d: Direction]: Position {
  -- pos_north_of_p (resp., pos_south_of_p, pos_east_of_p, and pos_west_of_p)
  -- consists of the position immediately north (resp. south, east, and west)
  -- of p, if such position exits. Otherwise, it is the empty set
  let pos_north_of_p = { q: Position | q.x = p.x and q.y = C/next[p.y] } |
  let pos_south_of_p = { q: Position | q.x = p.x and q.y = C/prev[p.y] } |
  let pos_east_of_p  = { q: Position | q.y = p.y and q.x = C/next[p.x] } |
  let pos_west_of_p  = { q: Position | q.y = p.y and q.x = C/prev[p.x] } |
    (d = North) => pos_north_of_p else
    (d = South) => pos_south_of_p else
    (d = East)  => pos_east_of_p else
                   pos_west_of_p
}
-- Note that pos_south_of_p, say, is empty if there is no position immediately 
-- south of p because in that case C/prev[p.y] is empty. Since q.y is a singleton
-- by definition of the Position signature, the condition of the comprehension 
-- expression is false, hence there are no q's that satisfy it.
-- The same argument applies to the other let variables.


---------------------
-- Transition system
---------------------

-- this predicate defines all possible transitions
pred transitions[t,t': Time] {
  some r: Rover |
    turn_on [r, t, t'] or
    turn_off [r, t, t'] or
    turn_left [r, t, t'] or
    turn_right [r, t, t'] or
    (some d: Direction | go [r, d, t, t'])
}


one sig R1 extends Rover {}
one sig P0 extends Position {}

-- P0 is the origin position of the coordinate system
fact {
 P0.x = C/first 
 P0.y = C/first
}

-- This predicate defines a possible initial state condition. 
-- It is satisfied by states in which rover R1 is at the origin position, 
-- facing East and turned off, while the other rovers, if any, are at
-- a different position than R1's 
pred init [t: Time] {
   R1.pos.t = P0
   R1.dir.t = East
   !is_on[R1, t] 
   all r: Rover - R1 | R1.pos.t != r.pos.t
}

-------------------
-- System predicate
-------------------
-- Denotes all possible executions of the system from a state
-- that satisfies the init condition
pred System {
	init [T/first]
  all t: Time - T/last | 
    transitions [t, T/next[t]]
}

-- Sample "goal" state condition.
-- The predicate is satisfied by states in which R1 is not 
-- at the origin and is facing north 
pred goal [t: Time] {
  R1.pos.t != P0
  R1.dir.t = North
}

-- This predicate holds iff it is possible for the transition system
-- to reach a state that satisfies the properties specified in goal,
-- when starting from an initial state satisfying the initial state
-- condition init
pred goalCheck {
 one Rover -- for simplicity
 System
 some t: Time | goal [t]
} 

-- check if the goal state is reachable
run goalCheck for 5




