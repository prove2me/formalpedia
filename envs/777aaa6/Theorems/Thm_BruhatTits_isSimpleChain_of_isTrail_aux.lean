-- Prove2me | Theorems.Thm_BruhatTits_isSimpleChain_of_isTrail_aux
-- name    : BruhatTits.isSimpleChain_of_isTrail_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:23:38.992333+00:00
-- url     : https://prove2.me/theorems/8e57b7c2-48f7-4c32-b992-a8c88695d7c4
-- title:
--   Bruhat Tits: is Simple Chain of is Trail aux
-- statement:
--   The Bruhat Tits construction uses the is Simple Chain of is Trail aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Tree.lean#L75-L116
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Tree.lean#L75-L116

import Definitions.Def_BruhatTits_Graph_GroupAction
import Definitions.Def_BruhatTits_Graph_Tree
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.isSimpleChain_of_isTrail_aux {x y : Vertices R} (p : BTgraph.Walk x y)
    (hp : p.IsTrail) (l : List (BruhatTits.Lattice R)) (hl : l.map (fun L ↦ ⟦L⟧) = p.support) :
    (List.zipWith₃ (fun L₁ _ L₃ ↦ ¬ Lattice.IsSimilar R L₁ L₃) l l.tail l.tail.tail).Forall id := by sorry
