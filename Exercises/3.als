module university
abstract sig educationalunit{
chairman:one professore,
research: one professore,
education: one professore

}


sig university extends educationalunit  {

}

sig campus  extends educationalunit{
belongsto:one university

}


sig department  extends educationalunit{


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
run show for 5  but exactly 1 group
