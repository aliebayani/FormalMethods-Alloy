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

	-- A person P's siblings are those people with the same parents as P (excluding P)
	all p: Person | p.siblings = {q: Person | p.parents = q.parents} - p

	-- Each married man (woman) has a wife (husband) 
	all p: Married | let s = p.spouse |
		(p in Man implies s in Woman) and
		(p in Woman implies s in Man)

	-- A spouse can't be a sibling
	no p: Married | p.spouse in p.siblings

}

----------------------------------------

/* Create an instance with at most three atoms in every top-level signature
 * (in this case just Person) 
 */
run {} for 3


