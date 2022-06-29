{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module SGD.DataPointDist where

import SGD.SGD

import Data.Dist
import Data.List
import Monad.Distr

-----------------------------------------------------------------
-- | instance Dist DataPoint ---------------------------------------
-----------------------------------------------------------------

{-@ reflect distDataPoint @-}
distDataPoint :: Dist DataPoint
distDataPoint = Dist distDP distEqDP triangularIneqDP symmetryDP

{-@ reflect distEqDP @-}
{-@ distEqDP :: x:DataPoint -> y:DataPoint -> {distDP x y = 0 <=> x = y} @-}
distEqDP :: DataPoint -> DataPoint -> ()
distEqDP (x, y) (x', y') | x <= x' && y <= y' = ()
distEqDP (x, y) (x', y') | x > x' && y <= y' = ()
distEqDP (x, y) (x', y') | x <= x' && y > y' = ()
distEqDP (x, y) (x', y') | x > x' && y > y' = ()
distEqDP _ _ = ()

{-@ reflect triangularIneqDP @-}
{-@ triangularIneqDP :: a:DataPoint -> b:DataPoint -> c:DataPoint -> { distDP a c <= distDP a b + distDP b c} @-}
triangularIneqDP :: DataPoint -> DataPoint -> DataPoint -> ()
triangularIneqDP _ _ _ = ()

{-@ reflect symmetryDP @-}
{-@ symmetryDP :: a:DataPoint -> b:DataPoint -> {distDP a b = distDP b a} @-}
symmetryDP :: DataPoint -> DataPoint -> () 
symmetryDP _ _ = ()

{-@ reflect distDP @-}
{-@ distDP :: DataPoint -> DataPoint -> {d:Double | 0.0 <= d } @-}
distDP :: DataPoint -> DataPoint -> Double 
distDP (x,y) (x',y') = distD x x' + distD y y'

