-- Prove2me | Theorems.Thm_BruhatTits_isStandard_of_list_isStandard
-- name    : BruhatTits.isStandard_of_list_isStandard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:23:47.872762+00:00
-- url     : https://prove2.me/theorems/a179de82-bb2e-41b3-8da5-58a5f9dfd149
-- title:
--   Bruhat Tits: is Standard of list is Standard
-- statement:
--   The Bruhat Tits construction uses the is Standard of list is Standard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Tree.lean#L133-L136
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Tree.lean#L133-L136

import Definitions.Def_BruhatTits_Graph_GroupAction
import Definitions.Def_BruhatTits_Graph_Tree
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.isStandard_of_list_isStandard {x y : Vertices R} {p : BTgraph.Walk x y}
    (l : List (BruhatTits.Lattice R)) (hleq : l.map (fun L ↦ ⟦L⟧) = p.support) (hl : l.IsStandard) :
    p.IsStandard := by sorry
