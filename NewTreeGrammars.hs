{-# LANGUAGE StandaloneDeriving #-}

module NewTreeGrammars where

import Data.Set (fromList, toList)

-- A little trick for eliminating duplicates from a list
set :: (Ord a) => [a] -> [a]
set xs = toList (fromList xs)

--------------------------------------------------------------------------------
-- Definitions of trees and finite-state tree automata.
-- We'll restrict attention to ranks zero, one and two. 
-- Given this restriction, specifying a ranked alphabet just amounts to 
-- specifying a set of rank zero symbols, a set of rank one symbols, and 
-- a set of rank two symbols. 
-- So instead of being parametrized by a ranked alphabet, our trees and 
-- automata will be parametrized by three types, one corresponding to 
-- each of these sets.

data Tree sy0 sy1 sy2 = Leaf sy0
                      | Unary sy1 (Tree sy0 sy1 sy2)
                      | Binary sy2 (Tree sy0 sy1 sy2) (Tree sy0 sy1 sy2)
                      deriving Show

type Automaton st sy0 sy1 sy2 = ([st], [(sy0,st)], [(st,sy1,st)], [(st,st,sy2,st)])

allStates :: (Ord st) => Automaton st sy0 sy1 sy2 -> [st]
allStates fsta =
    let (ends, nullaries, unaries, binaries) = fsta in
    set (
            ends
        ++  [q | (x,q) <- nullaries]
        ++  concat [[q',q] | (q',x,q) <- unaries]
        ++  concat [[q1',q2',q] | (q1',q2',x,q) <- binaries]
    )

--------------------------------------------------------------------------------
-- Here's how we would set up the ranked alphabet in (11a) on the handout

data Logic0 = Tru | Fls deriving (Show,Ord,Eq)
data Logic1 = Ng deriving (Show,Ord,Eq)
data Logic2 = Cnj | Dsj deriving (Show,Ord,Eq)

logictree :: Tree Logic0 Logic1 Logic2
logictree = Binary Dsj (Unary Ng (Leaf Tru)) (Binary Cnj (Leaf Fls) (Leaf Tru))

--------------------------------------------------------------------------------
-- Section 2.3.1 on the handout

data Sig0 = X | Y deriving (Show,Ord,Eq)
data Sig1 = F deriving (Show,Ord,Eq)
data Sig2 = G deriving (Show,Ord,Eq)

t15 :: Tree Sig0 Sig1 Sig2
t15 = Unary F (Binary G (Unary F (Leaf X)) (Binary G (Leaf X) (Leaf Y)))

data Parity = Even | Odd deriving (Show,Ord,Eq)

fsta_even :: Automaton Parity Sig0 Sig1 Sig2
fsta_even = ([Even],
             [(X,Odd), (Y,Even)], 
             [(Odd,F,Odd), (Even,F,Even)], 
             [(Odd,Odd,G,Even), (Odd,Even,G,Odd), (Even,Odd,G,Odd), (Even,Even,G,Even)])

-- Compare this function with the transitions of fsta_even!
evenXs :: Tree Sig0 Sig1 Sig2 -> Parity
evenXs (Leaf s) = case s of {X -> Odd; Y -> Even}
evenXs (Unary s t) = evenXs t
evenXs (Binary s t1 t2) =
    case (evenXs t1, evenXs t2) of
    (Odd,Odd) -> Even
    (Odd,Even) -> Odd
    (Even,Odd) -> Odd
    (Even,Even) -> Even

--------------------------------------------------------------------------------
data Gam1
deriving instance Eq Gam1   -- (a distracting but irrelevant wrinkle due to the fact that Gam1 is empty)
deriving instance Show Gam1 -- (a distracting but irrelevant wrinkle due to the fact that Gam1 is empty)
deriving instance Ord Gam1  -- (a distracting but irrelevant wrinkle due to the fact that Gam1 is empty)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

insideSet :: (Eq st, Eq sy0, Eq sy1, Eq sy2) => Automaton st sy0 sy1 sy2 -> Tree sy0 sy1 sy2 -> [st]
insideSet fsta tree =
    let (ends, nullaries, unaries, binaries) = fsta in
    case tree of
    Leaf x -> [q | (y,q) <- nullaries, y == x]
    Unary x t -> [q | (q',y,q) <- unaries, y == x, elem q' (insideSet fsta t)]
    Binary x t1 t2 -> [q | (q1,q2,y,q) <- binaries, y == x, elem q1 (insideSet fsta t1), 
                                                            elem q2 (insideSet fsta t2)]

recognize :: (Eq st, Eq sy0, Eq sy1, Eq sy2) => Automaton st sy0 sy1 sy2 -> Tree sy0 sy1 sy2 -> Bool
recognize fsta tree =
    let (ends, nullaries, unaries, binaries) = fsta in
    or [elem q ends | q <- insideSet fsta tree]

