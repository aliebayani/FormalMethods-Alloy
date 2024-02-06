module person
abstract sig person{
     mother: one woman,
    father: one man
}

fun grandpa(p:person): set(person){
  p.(mother+father).father
}
sig man extends person{}
sig woman extends person{}

pred show[p:person]{
 p in grandpa[p]
}

run show for 4 person
