-- Prove2me | Theorems.Thm_BruhatTits_eq_iff
-- name    : BruhatTits.eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:09:45.240958+00:00
-- url     : https://prove2.me/theorems/cc4d602a-e16a-40eb-8b36-8d4a13262de0
-- title:
--   Bruhat Tits: eq iff
-- statement:
--   Two vertices are equal if and only if their distance is zero.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L240-L248
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L240-L248

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}
open Pointwise

theorem BruhatTits.eq_iff (M L : Vertices R) : M = L ↔ inv M L = 0 := by sorry
