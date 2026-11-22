-- Prove2me | Theorems.Thm_BruhatTits_dist_BTgraph_eq_inv
-- name    : BruhatTits.dist_BTgraph_eq_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:24:40.832176+00:00
-- url     : https://prove2.me/theorems/4099865e-6a92-4e1c-bf50-b13fbe57b8db
-- title:
--   Bruhat Tits: dist BTgraph eq inv
-- statement:
--   The graph-theoretic distance agrees with our constructed `inv` function.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Tree.lean#L197-L200
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Tree.lean#L197-L200

import Definitions.Def_BruhatTits_Graph_GroupAction
import Definitions.Def_BruhatTits_Graph_Tree
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.dist_BTgraph_eq_inv : (BTgraph (R := R)).dist = inv := by sorry
