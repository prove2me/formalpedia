-- Prove2me | Theorems.Thm_BruhatTits_exists_map_isStandard
-- name    : BruhatTits.exists_map_isStandard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:24:13.771184+00:00
-- url     : https://prove2.me/theorems/0ddc96de-c87c-489e-b155-ec859e1d2935
-- title:
--   Bruhat Tits: exists map is Standard
-- statement:
--   Given two vertices and a trail `p` from `x` to `y`, there exists a `g : GL₂(K)`
--   such that `g • p` is a standard walk.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Tree.lean#L166-L179
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Tree.lean#L166-L179

import Definitions.Def_BruhatTits_Graph_GroupAction
import Definitions.Def_BruhatTits_Graph_Tree
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.exists_map_isStandard {x y : Vertices R} {p : BTgraph.Walk x y} (hp : p.IsTrail) :
    ∃ (g : GL (Fin 2) K), (p.map (g.toGraphIso (R := R))).IsStandard (R := R) := by sorry
