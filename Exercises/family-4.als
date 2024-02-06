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

---------------- Facts ----------------

fact {

	-- No person can be their own ancestor
	no p: Person | p in p.^parents

	-- No person can have more than one father or mother
	all p: Person | (lone (p.parents & Man)) and (lone (p.parents & Woman)) 

	-- A person P's siblings are those people with the same parentss as P (excluding P)
	all p: Person | p.siblings = {q: Person | p.parents = q.parents} - p

	-- Each married man (woman) has a wife (husband) 
	all p: Married | let s = p.spouse |
		(p in Man implies s in Woman) and
		(p in Woman implies s in Man)

	-- A spouse can't be a siblings
	no p: Married | p.spouse in p.siblings

}

---------------- Assertions ----------------

/* 
 * NOTE THAT AA ONLY EXECUTES THE FIRST execute-command (run OR check) IN THE FILE. 
 */

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
		some p.^parents & p.spouse.^parents
}
 check NoIncest

------------------- Run ---------------------

-- Make an instance with at most two atoms in every top-level signature (scope 2), 
-- and with a married man
run {some Man & Married} for 2

-- Make an instance with at most one atoms in every top-level signature, 
-- and with a married man (not satisfiable)
run {some Man & Married} for 1

-- There is no defined born on the number of atoms in the instance, so the 
-- default value is used. The default value is 3, thus this makes an instance 
-- with at most three atoms in every top-level signature, and with a married man
run {some Man & Married}

run {#Woman >= 1 and #Man = 0}		-- include a woman but no men
run {some Man and some Married and no Woman}	-- not satisfiable
run {some p: Person | some p.children}




