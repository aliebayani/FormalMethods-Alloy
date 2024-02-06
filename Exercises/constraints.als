//  Example signatures, declarations, and constraints

//  The motivations for this example are:
//    - people have friends, and a person can have a best friend
//       (but only one)
//    - a best friend is also a friend
//    - people can have dogs;  one person can have several
//    - dogs tend to focus on one person (their "owner", in this model)
//    - A proverb:  A dog is man's best friend.  So, what if someone's
//      best friend is a dog rather than a person?  What would that mean?

//  One way this might work out is to theorize that if a person's
//  best friend is a dog, it is going to be that person's dog
//  (not someone else's).
//  How would we say this in logic (and thus in Alloy)?

sig Dog {
  owner: lone Person   //  Each dog is focused on his/her owner.
                       //  But a stray dog could have 0 owners, so "lone".
}

sig Person {
  friend: set Person,  //  Any number of friends (0 to whatever)
  bestFriend:
    lone (Person+Dog), //  But at most only one best friend (0 or 1)
  dog: set Dog         //  Any number of dogs
}

//  This next thing is a signature fact -- it is only about Person
//  (the signature immediately before it).
//  Note the use of the "this" keyword,
//  and the absence of the "fact" keyword.
{
  this not in friend    //  We don't say that someone is their own friend.
}
//  Because it's a signature fact, we don't have to say which Person's
//  friend and best friend we are talking about -- it's as though we had
//  said
//    all p: Person | p not in p.friend
//  in an ordinary fact.

//  Can only have one signature fact, so this next one is just a fact
//  (with a "fact" keyword)
fact {
  bestFriend :> Person //  The part of the bestFriend relation
                       //  that links Persons to Persons (not to Dogs) ...
  in friend            //  is a sub-relation of friend.
}
//  That is, if someone's best friend is a person (not a dog),
//  then that best friend is also a friend.

fact {
  bestFriend :> Dog    //  The part of the bestFriend relation
                       //  that links Persons to Dogs ...
  in dog               //  is a sub-relation of dog.
}
//  That is, if someone's best friend is a dog (not a person),
//  then that dog is the person's dog.


pred show {}
run show

fact {
  all d: Dog |         //  For every dog,
  all p: d.owner |     //  ... the dog's owner ...
  d in p.dog           //  ... has that dog
}                      //  I don't think this can be made a signature fact
                       //  for either Dog or Person:
                       //  it talks about both Dogs and Persons.

assert dogOwnerAssert {//  I think this assertion says the same thing.
  owner                //  Dog -> lone Person
  in
  ~dog                 //  Dog -> Person
}
check dogOwnerAssert   //  So it should always be true (no counterexample).

assert ownerDogAssert {//  This assertion says something else
  dog                  //  Person -> Dog
  in
  ~owner               //  Person lone -> Dog
}
check ownerDogAssert   //  Alloy will find a counterexample for this.

//  To make ownerDogAssert valid, we need another fact (uncomment it):
//fact {
//  all p:Person | all d:p.dog | p = d.owner
//}

//  (Recall that "valid" means "true for every world".

