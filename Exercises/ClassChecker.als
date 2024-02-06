module ClassChecker

sig Class{
atts: set Attribute, 
ops: some Operation
}

sig Association {end1, end2: Mult one -> one Class}
sig Attribute {}
sig Operation {}
abstract sig Mult {}
one sig star extends Mult {}
one sig One extends Mult {}
one sig OneMany extends Mult {}
one sig Opt extends Mult {}

pred ShowCD {#Class > 2 and #Association > 1}
run ShowCD for 7