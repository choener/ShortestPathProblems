
module ShortestPath.SHP.Grammar.EdgeProb where

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
F -> mpty <<< ε       -- empty set
F -> node <<< s       -- single node
F -> edge <<< F k     -- edge k
L -> mpty <<< ε       -- empty set
L -> node <<< s       -- single node
L -> edge <<< L k     -- edge k
Z -> fini <<< L k F   -- edges bracketed by a Last and a First set
//
Emit: EdgeProb
|]

makeAlgebraProduct ''SigEdgeProb

