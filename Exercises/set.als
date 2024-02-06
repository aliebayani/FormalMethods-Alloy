//  Examples for sets

abstract sig Person {}
one sig Ann, Bob, Chip //  A set of three people
extends Person {}

abstract sig Dog {}
one sig Fido, Gruff, Hero //  A set of three dogs
extends Dog {}

pred show {}
run show

// assert noneInPerson {
//   none in Person
// }
//  alloy gives compilation warning that this is always true

// no, none
pred noNone {
  no none
}
run noNone

// in
assert personInUniv {
  Person in univ
}
check personInUniv

// +
assert dogInUnion {
  Dog in (Dog + Person)
}
check dogInUnion
//  Interesting that alloy doesn't warn of this at compile time

// assert noIntersection {
//   no (Dog & Person)
// }
//  alloy gives compilation warning that this is always true

// some, &
pred someIntersection {
  some (Dog & (Dog + Person))
}
run someIntersection

// -
pred someDifference {
  some univ - Person
}
run someDifference

// =
assert dogsTheDifference {
  Dog = ((Dog + Person) - Person)
}
check dogsTheDifference

