//  Quantifiers and predicates

abstract sig Person {           //  Signature
  child : set Person            //  Any number of children
                                //  (see <a href='#multiplicity'>set</a>)
}

fact {              //  (A fact about the model;  see <a href='#fact'>fact</a>)
  no p: Person |                //  No one ...
  p in p.^child                 //  ... is their own descendant
}

sig Man extends Person { }      //  Men are people

sig Woman extends Person { }    //  Women are people

//  Because both extend Person, everyone in this model is either
//  a man or a woman but not both.

fact {
  all p: Person |               //  Every person ...
  lone m: Man | p in m.child    //  ... has at most one father
}

fact {
  all p: Person |               //  Every person ...
  lone w: Woman | p in w.child  //  ... has at most one mother
}


fact {
  some Person                   //  Let's rule out the boring case of no people
}


pred show {}
run show

