module Spec.Utils where

import           Data.Sort                      ( sort )

clean :: (Ord a, Eq a) => [(a, Double)] -> [(a, Double)]
clean = foldr append [] . sort

append :: Eq a => (a, Double) -> [(a, Double)] -> [(a, Double)]
append (v', p') ((v, p):xs) | v == v' = (v, p + p'):xs
append x xs = x:xs
