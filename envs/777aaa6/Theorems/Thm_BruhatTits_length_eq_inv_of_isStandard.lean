-- Prove2me | Theorems.Thm_BruhatTits_length_eq_inv_of_isStandard
-- name    : BruhatTits.length_eq_inv_of_isStandard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:23:52.748296+00:00
-- url     : https://prove2.me/theorems/31bc47dd-d751-415c-bd70-3c2a66e7c5f2
-- title:
--   Bruhat Tits: length eq inv of is Standard
-- statement:
--   If `p` is a standard walk from `x` to `y`, the length of `p` is the distance `inv x y`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Tree.lean#L139-L162
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Tree.lean#L139-L162

import Definitions.Def_BruhatTits_Graph_GroupAction
import Definitions.Def_BruhatTits_Graph_Tree
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.length_eq_inv_of_isStandard {x y : Vertices R} {p : BTgraph.Walk x y} (h : p.IsStandard) :
    p.length = inv x y := by sorry
