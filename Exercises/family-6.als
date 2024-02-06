module family

---------------- Signatures ----------------

sig Time {}

abstract sig Person {
	children: Person set -> Time,
	parents: Person set -> Time,
	siblings: Person set -> Time,
	spouse: Person lone -> Time,
	alive: set Time
} 

sig Man, Woman extends Person {}

---------------- Predicate ----------------

-- Two persons are blood relatives at time t iff 
-- they have a common ancestor at time t
pred BloodRelatives [p: Person, q: Person, t: Time, ]  {
	some p.*(parents.t) & q.*(parents.t)
}

---------------- Fact ----------------

-- Define the parents relation
fact parentsDef {
      all t: Time | 
       parents.t = ~(children.t)
}

-- A person P's siblings are those people with the same parents as P (excluding P)
fact siblingsDef {
	all t: Time | all p: Person | 
    p.siblings.t = { q: Person - p | some q.parents.t and
                                     p.parents.t = q.parents.t }
}

fact staticOld {
	-- No person can be their own ancestor
	all t: Time | no p: Person | p in p.^(parents.t)

	-- No person can have more than one father or mother
	all t: Time | all p: Person | 
      lone (p.parents.t & Man) and 
      lone (p.parents.t & Woman)

	-- Each married man (woman) has a wife (husband) 
	all t: Time | all p: Person | 
        let s = p.spouse.t |
		  (p in Man implies s in Woman) and
		  (p in Woman implies s in Man)

	-- A spouse can't be a siblings
	all t: Time | no p: Person | 
           one p.spouse.t and p.spouse.t in p.siblings.t

	-- A person can't be married to a blood relative
	all t: Time | no p: Person | 
          one p.spouse.t and BloodRelatives [p, p.spouse.t, t]

	-- a person can't have children with a blood relative
	all t: Time | all p, q: Person |
		(some p.children.t & q.children.t and p != q) implies
                not BloodRelatives [p, q, t]
}


------------------- Run ---------------------

run {#Time > 1 and some p: Person | some p.children}  for 5



