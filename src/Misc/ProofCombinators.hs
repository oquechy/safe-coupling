module Misc.ProofCombinators where 

{-@ assert :: {b:Bool | b} -> {v:() | b } @-}
assert :: Bool -> () 
assert _ = ()

{-@ assume assume :: b:Bool -> {v:() | b } @-}
assume :: Bool -> () 
assume _ = ()

{-@ reflect using @-}
using :: a -> () -> a
using x _ = x