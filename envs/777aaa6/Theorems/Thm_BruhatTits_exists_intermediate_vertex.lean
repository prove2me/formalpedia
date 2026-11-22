-- Prove2me | Theorems.Thm_BruhatTits_exists_intermediate_vertex
-- name    : BruhatTits.exists_intermediate_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:09:10.239353+00:00
-- url     : https://prove2.me/theorems/80f21fbb-7419-4f67-ab6c-3e29debd61be
-- title:
--   Bruhat Tits: exists intermediate vertex
-- statement:
--   If vertices `x` and `y` have distance `n + 1`, there exists a vertex `o`
--   with `inv o x = 1` and `inv y o = n`.
--   This is the inductive step for showing that the Bruhat-Tits graph is connected
--   (see `BruhatTits.reachable`).
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L194-L218
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L194-L218

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}
open Pointwise

theorem BruhatTits.exists_intermediate_vertex (n : ℕ) (x y : Vertices R) (h : inv x y = n + 1) :
    ∃ (o : Vertices R), inv y o = n ∧ inv o x = 1 := by sorry
