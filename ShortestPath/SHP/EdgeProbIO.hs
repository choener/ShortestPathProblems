
module ShortestPath.SHP.EdgeProbIO where

import ADP.Fusion.Core
import FormalLanguage



[formalLanguage|
Verbose
Grammar: EdgeProb
N: F
N: L
N: Z
T: s
T: k
S: Z
-- inside
F -> mpty <<< ε       -- empty set
F -> node <<< F s     -- single node
F -> edge <<< F k     -- edge k
-- outside
L -> mpty <<< ε       -- full set
L -> node <<< L s     -- single node missing
L -> edge <<< L k     -- edge k removed
-- combine inside and outside
Z -> fini <<< F k L   -- edges bracketed by a Last and a First set
//
Emit: EdgeProb
|]

makeAlgebraProduct ''SigEdgeProb

