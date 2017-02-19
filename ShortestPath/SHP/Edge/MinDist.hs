
-- | Calculate minimum-distance Hamiltonian Shortest Paths and
-- probabilities for starting nodes.
--
-- NOTE: We explicitly model starting nodes. For symmetrical distance
-- matrices, this reports begin/end probabilities. For asymmetrical
-- distance matrices, a second instances with @Last@ instead of @First@
-- boundary should be created to calculate begin/end probabilities
-- separately.

module ShortestPath.SHP.Edge.MinDist where

import           Control.Arrow (second)
import           Control.Monad (forM_)
import           Data.List (nub,sort)
import           Data.Text (Text)
import           Debug.Trace
import           Numeric.Log
import qualified Data.Text as T
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import           Text.Printf

import           ADP.Fusion.Core
import           ADP.Fusion.Set1
import           ADP.Fusion.Unit
import           Data.PrimitiveArray hiding (toList)
import           Data.PrimitiveArray.ScoreMatrix
import           FormalLanguage
import           ShortestPath.SHP.Grammar.MinDist



-- | Minimal distance algebra
--
-- TODO The two Ints are the indices of the nodes and could be replaced?

aMinDist :: Monad m => ScoreMatrix Double -> SigMinDist m Double Double (From:.To) (Int:.To)
aMinDist s = SigMinDist
  { edge = \x (From f:.To t) ->
      let z = s .!. (f,t)
      in
#ifdef ADPFUSION_DEBUGOUTPUT
         traceShow (x,f,t,z) $
#endif
         x + z
  , mpty = \() ->
#ifdef ADPFUSION_DEBUGOUTPUT
      traceShow "empty" $
#endif
      0
  , node = \n ->
#ifdef ADPFUSION_DEBUGOUTPUT
      traceShow ("node",n) $
#endif
      0
  , fini = id
  , h    = SM.foldl' min 999999
  }
{-# Inline aMinDist #-}

-- | Maximum edge probability following the probabilities generated from
-- the @EdgeProb@ grammar.

aMaxEdgeProb :: Monad m => ScoreMatrix (Log Double) -> SigMinDist m (Log Double) (Log Double) (From:.To) (Int:.To)
aMaxEdgeProb s = SigMinDist
  { edge = \x (From f:.To t) -> x * (s .!. (f,t))
  , mpty = \() -> 1
  , node = \(_:.To n) -> let z = s `nodeDist` n in z
  , fini = id
  , h    = SM.foldl' max 0
  }
{-# Inline aMaxEdgeProb #-}

data PathBT
  = BTnode !(Int:.To)
  | BTedge !(From:.To)
  deriving (Show)

-- | This should give the correct order of nodes independent of the
-- underlying @Set1 First@ or @Set1 Last@ because the @(From:.To)@ system
-- is agnostic over these.

aPathBT :: Monad m => ScoreMatrix t -> SigMinDist m [PathBT] [[PathBT]] (From:.To) (Int:.To)
aPathBT s = SigMinDist
  { edge = \x e -> BTedge e : x
  , mpty = \()  -> []
  , node = \n   -> [BTnode n]
  , fini = id
  , h    = SM.toList
  }
{-# Inline aPathBT #-}

-- | This should give the correct order of nodes independent of the
-- underlying @Set1 First@ or @Set1 Last@ because the @(From:.To)@ system
-- is agnostic over these.

aPretty :: Monad m => ScoreMatrix t -> SigMinDist m Text [Text] (From:.To) (Int:.To)
aPretty s = SigMinDist
  { edge = \x (From f:.To t) -> T.concat [s `rowNameOf` f, T.pack " -> ", x]
  , mpty = \()  -> T.empty
  , node = \(_:.To n)   -> s `rowNameOf` n -- ok because it is the first node in the path
  , fini = id
  , h    = SM.toList
  }
{-# Inline aPretty #-}

-- | Before using @aInside@ the @ScoreMatrix@ needs to be scaled
-- appropriately! Due to performance reasons we don't want to do this
-- within @aInside@.

aInside :: Monad m => ScoreMatrix (Log Double) -> SigMinDist m (Log Double) (Log Double) (From:.To) (Int:.To)
aInside s = SigMinDist
  { edge = \x (From f:.To t) -> s .!. (f,t) * x
  , mpty = \() -> 1
  , node = \n -> 1
  , fini = id
  , h    = SM.foldl' (+) 0
  }
{-# Inline aInside #-}



type TS1 x = TwITbl Id Unboxed EmptyOk (BS1 First I)      x
type U   x = TwITbl Id Unboxed EmptyOk (Unit I)           x
type PF  x = TwITbl Id Unboxed EmptyOk (Boundary First I) x

type BT1 x b = TwITblBt Unboxed EmptyOk (BS1 First I) x Id Id b
type BTU x b = TwITblBt Unboxed EmptyOk (Unit I)      x Id Id b



-- | Run the minimal distance algebra.
--
-- This produces one-boundary sets. Meaning that for each boundary we get
-- the total distance within the set.

forwardMinDist1 :: ScoreMatrix Double -> Z:.TS1 Double:.U Double
forwardMinDist1 scoreMat =
  let n = numRows scoreMat
  in  mutateTablesST $ gMinDist (aMinDist scoreMat)
        (ITbl 0 0 EmptyOk (fromAssocs (BS1 0 (-1)) (BS1 (2^n-1) (Boundary $ n-1)) (-999999) []))
        (ITbl 1 0 EmptyOk (fromAssocs Unit         Unit                           (-999999) []))
        Edge
        Singleton
{-# NoInline forwardMinDist1 #-}

backtrackMinDist1 :: ScoreMatrix Double -> Z:.TS1 Double:.U Double -> [Text]
backtrackMinDist1 scoreMat (Z:.ts1:.u) = unId $ axiom b
  where !(Z:.bt1:.b) = gMinDist (aMinDist scoreMat <|| aPretty scoreMat)
                            (toBacktrack ts1 (undefined :: Id a -> Id a))
                            (toBacktrack u   (undefined :: Id a -> Id a))
                            Edge
                            Singleton
                        :: Z:.BT1 Double Text:.BTU Double Text
{-# NoInline backtrackMinDist1 #-}

pathbtMinDist :: ScoreMatrix Double -> Z:.TS1 Double:.U Double -> [[PathBT]]
pathbtMinDist scoreMat (Z:.ts1:.u) = unId $ axiom b
  where !(Z:.bt1:.b) = gMinDist (aMinDist scoreMat <|| aPathBT scoreMat)
                            (toBacktrack ts1 (undefined :: Id a -> Id a))
                            (toBacktrack u   (undefined :: Id a -> Id a))
                            Edge
                            Singleton
                        :: Z:.BT1 Double [PathBT]:.BTU Double [PathBT]
{-# NoInline pathbtMinDist #-}

-- | Given the @Set1@ produced in @forwardMinDist1@ we can now extract the
-- co-optimal paths using the @Set1 -> ()@ index change.
--
-- TODO do we want this one explicitly or make life easy and just extract
-- from all @forwardMinDist1@ paths?

runCoOptDist :: ScoreMatrix Double -> (Double,[Text])
runCoOptDist scoreMat = (unId $ axiom fwdu,bs)
  where !(Z:.fwd1:.fwdu) = forwardMinDist1 scoreMat
        bs = backtrackMinDist1 scoreMat (Z:.fwd1:.fwdu)
{-# NoInline runCoOptDist #-}

-- | Return the minimal distance and provide a list of co-optimal
-- backtraces.

runMinDist :: ScoreMatrix Double -> (Double,[[PathBT]])
runMinDist scoreMat = (unId $ axiom fwdu,bs)
  where !(Z:.fwd1:.fwdu) = forwardMinDist1 scoreMat
        bs = pathbtMinDist scoreMat (Z:.fwd1:.fwdu)
{-# NoInline runMinDist #-}

-- | Extract the individual partition scores.

boundaryPartFun :: Double -> ScoreMatrix Double -> [(Boundary First I,Log Double)]
boundaryPartFun temperature scoreMat =
  let n       = numRows scoreMat
      partMat = toPartMatrix temperature scoreMat
      (Z:.sM:.bM) = mutateTablesST $ gMinDist (aInside partMat)
                      (ITbl 0 0 EmptyOk (fromAssocs (BS1 0 (-1)) (BS1 (2^n-1) (Boundary $ n-1)) (-999999) []))
                      (ITbl 1 0 EmptyOk (fromAssocs (Boundary 0) (Boundary $ n-1)               (-999999) []))
                      Edge
                      Singleton
                    :: Z:.TS1 (Log Double):.PF (Log Double)
      TW (ITbl _ _ _ pf) _ = bM
      bs' = assocs pf
      pssum = Numeric.Log.sum $ Prelude.map snd bs'
      bs = Prelude.map (second (/pssum)) bs'
  in bs

{-# NoInline boundaryPartFun #-}

-- | Run the maximal edge probability grammar.

forwardMaxEdgeProb :: ScoreMatrix (Log Double) -> Z:.TS1 (Log Double):.U (Log Double)
forwardMaxEdgeProb scoreMat =
  let n = numRows scoreMat
  in  mutateTablesST $ gMinDist (aMaxEdgeProb scoreMat)
        (ITbl 0 0 EmptyOk (fromAssocs (BS1 0 (-1)) (BS1 (2^n-1) (Boundary $ n-1)) 0 []))
        (ITbl 1 0 EmptyOk (fromAssocs Unit         Unit                           0 []))
        Edge
        Singleton
{-# NoInline forwardMaxEdgeProb #-}

pathbtMaxEdgeProb :: ScoreMatrix (Log Double) -> Z:.TS1 (Log Double):.U (Log Double) -> [[PathBT]]
pathbtMaxEdgeProb scoreMat (Z:.ts1:.u) = unId $ axiom b
  where !(Z:.bt1:.b) = gMinDist (aMaxEdgeProb scoreMat <|| aPathBT scoreMat)
                            (toBacktrack ts1 (undefined :: Id a -> Id a))
                            (toBacktrack u   (undefined :: Id a -> Id a))
                            Edge
                            Singleton
                        :: Z:.BT1 (Log Double) [PathBT]:.BTU (Log Double) [PathBT]
{-# NoInline pathbtMaxEdgeProb #-}

-- | Given the @Set1@ produced in @forwardMinDist1@ we can now extract the
-- co-optimal paths using the @Set1 -> ()@ index change.
--
-- TODO do we want this one explicitly or make life easy and just extract
-- from all @forwardMinDist1@ paths?

runMaxEdgeProb :: ScoreMatrix (Log Double) -> (Log Double,[[PathBT]])
runMaxEdgeProb scoreMat = (unId $ axiom fwdu,bs)
  where !(Z:.fwd1:.fwdu) = forwardMaxEdgeProb scoreMat
        bs = pathbtMaxEdgeProb scoreMat (Z:.fwd1:.fwdu)
{-# NoInline runMaxEdgeProb #-}



test t fp = do
  sMat <- fromFile fp
  print sMat
  let (d,bt) = runCoOptDist sMat
  print d
  mapM_ print $ bt
  print $ length bt
  print $ length $ nub $ sort bt
  let (dmin,btmin) = runMinDist sMat
  print dmin
  mapM_ print $ btmin
  let ps = boundaryPartFun t sMat
  forM_ ps $ \(b,_) -> printf "%5s  " (sMat `rowNameOf` getBoundary b)
  putStrLn ""
  forM_ ps $ \(_,Exp p) -> printf "%0.3f  " (exp p)
  putStrLn ""
{-# NoInline test #-}

