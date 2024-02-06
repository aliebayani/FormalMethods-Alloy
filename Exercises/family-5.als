---------------- Signatures ----------------

abstract sig Person {
	children: set Person,
	siblings: set Person
} 

sig Man, Woman extends Person {}

sig Married in Person {
	spouse: one Married 
}
---------------- Functions ----------------

-- Define the parents relation as an auxiliary one
fun parents [] : Person -> Person { ~children }

---------------- Predicate ----------------

-- Two persons are blood relatives iff they have a common ancestor
pred BloodRelatives [p: Person, q: Person] {
	some p.*parents & q.*parents
}

---------------- Facts ----------------

fact {

	-- No person can be their own ancestor
	no p: Person | p in p.^parents

	-- No person can have more than one father or mother
	all p: Person | (lone (p.parents & Man)) and (lone (p.parents & Woman)) 

	-- A person P's siblingss are those people with the same parentss as P (excluding P)
	all p: Person | p.siblings = {q: Person | p.parents = q.parents} - p

	-- Each married man (woman) has a wife (husband) 
	all p: Married | let s = p.spouse |
		(p in Man implies s in Woman) and
		(p in Woman implies s in Man)

	-- A spouse can't be a siblings
	no p: Married | p.spouse in p.siblings

	-- A person can't be married to a blood relative
	no p: Married | BloodRelatives [p, p.spouse]

	-- A person can't have children with a blood relative
	all p, q: Person |
		(some p.children & q.children and p != q) implies
        not BloodRelatives [p, q]
}

---------------- Assertions ----------------

-- No person has a parents that's also a siblings.
assert parentsArentsiblings {    
	all p: Person | no p.parents & p.siblings 
}
check parentsArentsiblings for 10

-- Every person's siblings are his/her siblings' siblings. 
assert siblingsSiblings {
	all p: Person | p.siblings = p.siblings.siblings
}
check siblingsSiblings

-- No person shares a common ancestor with his spouse (i.e., spouse isn't related by blood). 
assert NoIncest {
	no p: Married | 
		some (p.^parents & p.spouse.^parents)
}
check NoIncest

------------------- Run ---------------------

run {some Man & Married} for 1		-- with a scope 1 and include a married man (not satisfiable)
run {some Man & Married} for 2		-- with a scope 2 and include a married man
run {some Man & Married}			-- with a scope 3 and include a married man

run {#Woman >= 1 and #Man = 0}			-- include a woman but no men
run {some Man and some Married and no Woman}		-- not satisfiable
run {some p: Person | some p.children}




