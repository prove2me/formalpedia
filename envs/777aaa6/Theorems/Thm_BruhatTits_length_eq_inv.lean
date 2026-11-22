-- Prove2me | Theorems.Thm_BruhatTits_length_eq_inv
-- name    : BruhatTits.length_eq_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:24:08.497182+00:00
-- url     : https://prove2.me/theorems/5cc98208-169f-4a10-ab02-e545be1ebb0c
-- title:
--   Bruhat Tits: length eq inv
-- statement:
--   The length of a trail is equal to the distance of the endpoints.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Tree.lean#L186-L194
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Tree.lean#L186-L194

import Definitions.Def_BruhatTits_Graph_GroupAction
import Definitions.Def_BruhatTits_Graph_Tree
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.length_eq_inv {x y : Vertices R} {p : BTgraph.Walk x y} (hp : p.IsTrail) :
    p.length = inv x y := by sorry
