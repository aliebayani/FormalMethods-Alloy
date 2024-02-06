module examples/hotel
open util/ordering [Time] as TO
open util/ordering [Key] as KO
sig Key {}
sig Time {}
sig Room {
  keys: set Key,
  currentKey: Key one -> Time
}
sig Guest {
  gkeys: Key -> Time
}
one sig FrontDesk {
 lastKey: (Room -> lone Key) -> Time,
 occupant: Room -> Guest -> Time
}


fact {
all k: Key | lone keys.k
all r:Room, t:Time| r.currentKey.t in r.keys 
}

fun nextKey [k: Key, ks: set Key]: set Key
{
	KO/min [KO/nexts[k] & ks]
}

pred init [t: Time] {
	-- no guests have keys
	no Guest.gkeys.t
	-- the roster at the front desk shows
	-- no room as occupied
	no FrontDesk.occupant.t
	-- the record of each room’s key at the
	-- front desk is synchronized with the
	-- current combination of the lock itself
	all r: Room | 
	 r.(FrontDesk.lastKey.t) = r.currentKey.t
}

pred entry [ g: Guest, r: Room, k: Key, 
					 t, t': Time ] {
	-- the key used to open the lock is one of
	-- the key the guest holding
	k in g.gkeys.t
	-- pre and post conditions
	let ck = r.currentKey |
		-- not a new guest
		(k = ck.t and ck.t' = ck.t) or 
		-- new guest
		(k = nextKey [ck.t, r.keys] and ck.t' = k)
	-- frame conditions
	noRoomChangeExcept [r, t, t']
	noGuestChangeExcept [none, t, t']
	noFrontDeskChange [t, t']
}

pred noFrontDeskChange [t,t': Time] 
{
	FrontDesk.lastKey.t = FrontDesk.lastKey.t'
	FrontDesk.occupant.t = FrontDesk.occupant.t'
}
pred noRoomChangeExcept [rs: set Room, t,t': Time]
{
	all r: Room - rs |
		r.currentKey.t = r.currentKey.t'
}
pred noGuestChangeExcept [gs: set Guest, t,t': Time] 
{
	all g: Guest - gs | g.gkeys.t = g.gkeys.t'
}

pred checkout [ g: Guest, t,t': Time ]
{
	let occ = FrontDesk.occupant | {
	  -- the guest occupies one or more rooms
	  some occ.t.g
	  -- the guest’s room become available
	  occ.t' = occ.t - (Room -> g)
	}
	-- frame condition
	FrontDesk.lastKey.t = FrontDesk.lastKey.t'
	noRoomChangeExcept [none, t, t']
	noGuestChangeExcept [none, t, t']
}

pred checkin [ g: Guest, r: Room, k: Key, t,t': Time ] {
	-- the guest holds the input key 
	g.gkeys.t' = g.gkeys.t + k
	let occ = FrontDesk.occupant | {
		-- the room has no current occupant
		no r.occ.t
		-- the guest becomes the new occupant of the room
		occ.t' = occ.t + r->g 
	}
	let lk = FrontDesk.lastKey | {
		-- the input key becomes the room’s current key
		lk.t' = lk.t ++ r->k
		-- the input key is the successor of the last key in 
		-- the sequence associated to the room
		k = nextKey [r.lk.t, r.keys]
	}
	noRoomChangeExcept [none, t, t']
	noGuestChangeExcept [g, t, t']
}

fact Traces {
	init [TO/first]
	all t: Time - TO/last |
	let t' = TO/next [t] | 
	some g: Guest, r: Room, k: Key |
		entry [g, r, k, t, t'] or
		checkin [g, r, k, t, t'] or
		checkout [g, t, t'] 
}
assert noBadEntry  {
	all t: Time, r: Room, g: Guest, k: Key | let t' = TO/next [t],
      o = r.(FrontDesk.occupant).t |
		(entry [g, r, k, t, t'] and some o)
			implies g in o
}

check noBadEntry for 3 
but 2 Room, 2 Guest, 5 Time
