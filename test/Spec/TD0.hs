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

v0 :: ValueFunction
v0 = Cons 1.0 (Cons (-1.0) Nil)

unit_td0_base :: Assertion
unit_td0_base = do
  eqVf v (map ppure v0) @? "value function want " ++ show v0 ++ " got " ++ show v
  where v = td0 0 undefined undefined undefined v0

unit_td0_simple :: Assertion
unit_td0_simple = do
  eqVf v (map ppure (Cons 0.36 (Cons (-0.14) Nil))) @? "value function want " ++ show v0 ++ " got " ++ show v
  where 
      v = td0 2 π r p v0
      π = const (ppure 0)
      r = const (const (ppure 0))
      p = const (const (const (ppure 0)))
