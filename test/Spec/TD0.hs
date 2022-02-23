{-# LANGUAGE PackageImports #-}
{-@ LIQUID "--reflection" @-}

module Spec.TD0 where

import           Test.HUnit                     ( assertEqual
                                                , (@?)
                                                , (@?=)
                                                , Assertion
                                                )
import           TD0                            ( td0
                                                , ValueFunction
                                                , Transition
                                                )

import           Monad.Implemented.Distr
import           Data.Dist
import "SGD-verified" Data.List

import           Prelude                 hiding ( map
                                                , repeat
                                                , foldr
                                                , fmap
                                                , mapM
                                                )

import           Numeric.Probability.Distribution
                                                ( decons )

v0 :: ValueFunction
v0 = Cons 1.0 (Cons (-1.0) Nil)

t :: Transition
t = Cons (ppure (0, 0)) (Cons (ppure (0, 0)) Nil)

unit_td0_base :: Assertion
unit_td0_base =
  v @?= v0 
  where [(v, 1)] = decons $ td0 0 v0 undefined

unit_td0_simple :: Assertion
unit_td0_simple =
  v @?= Cons 0.36 (Cons (-0.14) Nil)
  where 
      [(v, 1)] = decons $ td0 2 v0 t 
      