module university
sig university{
chairman:one professore,
research: one professore,
education: one professore,
account:one employee
}

sig campus{
belongsto:one university,
chairman:one professore,
research: one professore,
education: one professore,
account:one employee
}


sig department{
chairman:one professore,
research: one professore,
education: one professore,
account:one employee
}


sig group{
head: one professore 
}


sig professore{
worksat: one group,
member: one group
}

sig student {
studiesat: one group

}

sig employee{
worksat:one group
}

pred show(){}
run show
