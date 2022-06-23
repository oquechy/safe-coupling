{-# LANGUAGE PackageImports #-}
{-@ LIQUID "--reflection" @-}

module Spec.TD0 where

import           Test.HUnit                     ( assertEqual
                                                , (@?)
                                                , (@?=)
                                                , Assertion
                                                )
import           TD.TD0                         ( td0
                                                , ValueFunction
                                                , Transition
                                                )

import           Monad.Distr
import           Data.Dist
import "safe-coupling" Data.List

import           Prelude                 hiding ( map
                                                , repeat
                                                , foldr
                                                , fmap
                                                , mapM
                                                )

import           Numeric.Probability.Distribution
                                                ( decons )

v0 :: ValueFunction
v0 = [1.0, -1.0]

t :: Transition
t = [ppure (0, 0), ppure (0, 0)]

unit_td0_base :: Assertion
unit_td0_base =
  v @?= v0 
  where [(v, 1)] = decons $ td0 0 v0 t

unit_td0_simple :: Assertion
unit_td0_simple =
  v @?= [0.36, -0.14]
  where 
      [(v, 1)] = decons $ td0 2 v0 t 
      