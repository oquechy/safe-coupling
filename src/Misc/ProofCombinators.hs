module Misc.ProofCombinators where 


{-@ assert :: {b:Bool | b} -> {v:() | b } @-}
assert :: Bool -> () 
assert _ = ()

{-@ assume assume :: b:Bool -> {v:() | b } @-}
assume :: Bool -> () 
assume _ = ()
