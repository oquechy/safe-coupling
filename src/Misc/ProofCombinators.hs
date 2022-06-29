module Misc.ProofCombinators where 


{-@ assert :: {b:Bool | b} -> {v:() | b } @-}
assert :: Bool -> () 
assert _ = ()

{-@ assume assume :: b:Bool -> {v:() | b } @-}
assume :: Bool -> () 
assume _ = ()

{-@ assertWith :: Bool -> () -> () @-}
assertWith :: Bool -> () -> ()
assertWith _ x = x