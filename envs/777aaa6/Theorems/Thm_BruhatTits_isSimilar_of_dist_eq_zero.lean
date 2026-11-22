-- Prove2me | Theorems.Thm_BruhatTits_isSimilar_of_dist_eq_zero
-- name    : BruhatTits.isSimilar_of_dist_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:09:19.892172+00:00
-- url     : https://prove2.me/theorems/d5216c93-4692-421d-88b2-7bb8cbc4fadd
-- title:
--   Bruhat Tits: is Similar of dist eq zero
-- statement:
--   If two lattices have distance zero, they are equal up to a unit.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L221-L237
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L221-L237

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}
open Pointwise

theorem BruhatTits.isSimilar_of_dist_eq_zero {M L : BruhatTits.Lattice R} (h : dist M L = 0) :
    Lattice.IsSimilar R M L := by sorry
