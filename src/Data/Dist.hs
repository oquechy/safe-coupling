{-@ LIQUID "--reflection" @-}

module Data.Dist
  ( dist
  )
where

{-@ measure dist :: a -> a -> Double @-}
{-@ assume dist :: x1:_ -> x2:_ -> {v:Double | v == dist x1 x2 } @-}
dist :: a -> a -> Double
dist _ _ = 0
