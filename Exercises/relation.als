//  Relations and logic

abstract sig Dog { }
one sig Fido, Gruff, Hero //  A set of three dogs
extends Dog {}

abstract sig Person {
  hasOneDog: Dog,
  hasDogs: some Dog,
  bestFriend: one Person
}
one sig Ann, Bob, Chip //  A set of three people
extends Person {}


pred show {}
run show

// arrow product ->
fun x: Person->Dog {
  Ann->Fido +
  Bob->Fido +
  Chip->Gruff
}
pred xInHasDogs {
  x in hasDogs
}
run xInHasDogs

// dot join .
pred fidoInOne {
  Fido in
  Person.hasOneDog     //  Somebody has Fido as only dog.
}
run fidoInOne

pred fidoInSome {
  Fido in
  Person.hasDogs       //  Somebody has Fido as one of their dogs
}
run fidoInSome

// dot join and quantifier
pred fidoInEvery {
  all p:Person |
  Fido in p.hasDogs    //  Everybody has Fido as one of their dogs
}
run fidoInEvery

// box join []
pred dogInEvery {
  Dog in
  hasOneDog[Person]    // fidoInOne, reversed (box)
}
run dogInEvery

// transpose ~
pred chipInEvery {
  Chip in
  Dog.~hasOneDog       //  Chip in transposed hasOneDog
}
run chipInEvery

// transitive closure ^
pred closing {
  Bob not in Ann.bestFriend
  and
  Bob in Ann.^bestFriend
}
run closing

// domain restriction <:
// range restriction :>
pred restrictions {
  (Person <: iden :> Dog)
  in hasOneDog         //  Restrictions on iden
}
run restrictions

// override ++
pred override [p:Person->Dog] {
  p not in
  (hasOneDog
  ++
  Ann->Gruff)          //  Overriding every tuple beginning with Ann
}
run override

