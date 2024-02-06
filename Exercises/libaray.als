module LibrarySys

sig Title{}
sig Book {name: Title}
fact UniqueTitles {all t: Title | one name.t}

abstract sig Copy{description: Book}
sig Reference extends Copy {}
sig General extends Copy {}

abstract sig Borrower {checkedout: set General}
sig Student extends Borrower{}{#checkedout =< 3}
sig Faculty extends Borrower{}

fact OneCheckOut {all c: General | lone checkedout.c}

pred ShowBorr[b: Borrower]{some b.checkedout}
run ShowBorr for 5

assert NoMultCheckouts {all c: General | #checkedout.c < 2}
check NoMultCheckouts for 10