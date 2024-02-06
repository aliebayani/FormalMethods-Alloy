// disj

abstract sig Person {
  likes: Person
}
one sig Ann, Bob, Chip //  A world of three people
extends Person {}

pred show {}
run show

pred friends [p,q: Person] {
  p in q.likes         //  q likes p
  and
  q in p.likes         //  p likes q
}
run friends            //  p and q can be same person

pred friendsDisj [disj p,q: Person] {
                       //  p and q must be different people
  p in q.likes         //  q likes p
  and
  q in p.likes         //  p likes q
}
run friendsDisj        //  probably what was expected

