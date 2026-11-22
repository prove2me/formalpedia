-- Prove2me | Theorems.Thm_SimpleGraph_Walk_exists_repr_isChain
-- name    : SimpleGraph.Walk.exists_repr_isChain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:23:40.621488+00:00
-- url     : https://prove2.me/theorems/dcc9e3e7-e667-4d03-ad09-61dc3ed7ec61
-- title:
--   Walk: exists repr is Chain
-- statement:
--   Any walk is representable by a chain of lattices. If the walk is a trail,
--   the chain is simple (see `BruhatTits.exists_repr_isSimpleChain_of_isTrail`).
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Tree.lean#L38-L59
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Tree.lean#L38-L59

import Definitions.Def_BruhatTits_Graph_GroupAction
import Definitions.Def_BruhatTits_Graph_Tree
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem SimpleGraph.Walk.exists_repr_isChain {x y : Vertices R} (p : BTgraph.Walk x y) :
    ∃ (l : List (BruhatTits.Lattice R)), l.IsBruhatTitsChain ∧ l.map (fun L ↦ ⟦L⟧) = p.support := by sorry
