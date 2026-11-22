-- Prove2me | Theorems.Thm_BruhatTits_exists_repr_isSimpleChain_of_isTrail
-- name    : BruhatTits.exists_repr_isSimpleChain_of_isTrail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:23:36.050101+00:00
-- url     : https://prove2.me/theorems/6a468512-2695-4cdf-b4d0-93b8a4fe1b18
-- title:
--   Bruhat Tits: exists repr is Simple Chain of is Trail
-- statement:
--   If `p` is a trail in the Bruhat-Tits graph, it is representable by
--     a simple chain of lattices.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Tree.lean#L120-L125
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Tree.lean#L120-L125

import Definitions.Def_BruhatTits_Graph_GroupAction
import Definitions.Def_BruhatTits_Graph_Tree
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.exists_repr_isSimpleChain_of_isTrail {x y : Vertices R} (p : BTgraph.Walk x y)
    (hp : p.IsTrail) :
    ∃ (l : List (BruhatTits.Lattice R)), l.IsSimpleChain ∧ l.map (fun L ↦ ⟦L⟧) = p.support := by sorry
