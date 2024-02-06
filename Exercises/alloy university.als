module university

abstract sig educationalunit {
	chairman: one professor,
	research: one professor, 
	educational: one professor
}

sig university extends educationalunit { }

sig campus extends educationalunit {
	belongsto: one university 
}

sig department extends educationalunit { }

sig group {
	head: one professor,
	belongsto: one department
}

sig professor {
	worksat: one group,
	member: one group
}

sig student {
	studiesat: one group
}

sig employee {
	worksat: one group
}

pred show(){}
run show {}

 
