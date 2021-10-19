{-@ LIQUID "--reflection" @-}

module Data.Dist where 

{-@ measure dist :: a -> a -> Double @-}
{-@ assume dist :: x1:a -> x2:a -> {v:Double | v == dist x1 x2 } @-}
dist :: a -> a -> Double
dist _ _ = 0
