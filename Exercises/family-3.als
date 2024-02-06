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

-- Define the parent relation as an auxiliary one
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

------------------- Run ---------------------

/* 
 * NOTE THAT AA ONLY EXECUTES THE FIRST run IN THE FILE. SO YOU HAVE TO COMMENT  
 * PREVIOUS run commands or use the AA "Execute" pull-down menu 
 */

-- Create an instance with at most two atoms in every top-level signature (scope 2), 
-- and with a married man
run {some Man & Married} for 2

-- Create an instance with at most one atom in every top-level signature, 
-- and with a married man (not satisfiable)
run {some Man &  Married} for 1

-- Create an instance using defaul scopes (3).
run {some Man & Married}

run {#Woman >= 1 and #Man = 0}		-- include a woman but no men
run {some Man and some Married and no Woman}	-- not satisfiable
run {some p: Person | some p.children}




