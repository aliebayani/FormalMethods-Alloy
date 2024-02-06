//  Else

abstract sig A {}
sig B extends A {}

pred true {      //  Always true
  some a:A | a in A
}
run true

pred false {     //  Always false
  some a:A | a not in A
}
run false

pred elseTTT {  true  implies true  else true   }
run  elseTTT           //  should be true

pred elseTTF {  true  implies true  else false  }
run  elseTTF           //  should be true

pred elseTFT {  true  implies false else true   }
run  elseTFT           //  should be FALSE

pred elseTFF {  true  implies false else false  }
run  elseTFF           //  should be FALSE

pred elseFTT {  false implies true  else true   }
run  elseFTT           //  should be true

pred elseFTF {  false implies true  else false  }
run  elseFTF           //  should be FALSE

pred elseFFT {  false implies false else true   }
run  elseFFT           //  should be true

pred elseFFF {  false implies false else false  }
run  elseFFF           //  should be FALSE

