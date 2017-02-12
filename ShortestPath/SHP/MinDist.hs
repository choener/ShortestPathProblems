
module ShortestPath.SHP.MinDist where

import ADP.Fusion.Core
import FormalLanguage



-- A small grammar for Hamiltonian path problems. We need three rules due
-- to normalization requirements for Inside-Outside.
--
-- Now, not a single node is set.
--
-- @
-- X -> mpty <<< e
-- @
--
-- A single node may be inserted, if the remainder of the set is then
-- empty. This means that the @s@ terminal checks that only sets of size
-- one are looked at.
--
-- @
-- X -> node <<< s X
-- @
--
-- An edge @k@ can be inserted, if at least one element in the set is still
-- empty, and the set already contains at least one element.
--
-- @
-- X -> edge <<< k X
-- @
--
-- TODO generalize to be SHP and move into shortest path problem library

[formalLanguage|
Verbose
Grammar: MinDist
N: X
N: Y
T: s
T: k
S: Y
X -> mpty <<< ε     -- empty set
X -> node <<< s     -- single node
X -> edge <<< X k   -- edge k
Y -> fini <<< X     -- extract just the co-optimal ones
//
Emit: MinDist
|]

makeAlgebraProduct ''SigMinDist


