-- Prove2me | Theorems.Thm_BruhatTits_dist_inv_isSimilar
-- name    : BruhatTits.dist_inv_isSimilar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:48:33.927924+00:00
-- url     : https://prove2.me/theorems/3302fde0-d1c5-4553-a34d-c6b25be95b0d
-- title:
--   Bruhat Tits: dist inv is Similar
-- statement:
--   The distance of lattices is invariant under the equivalence relation `IsSimilar`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L483-L489
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L483-L489

import Definitions.Def_BruhatTits_Cartan_Uniqueness
import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Lattice_Distance
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
open Algebra BruhatTits Matrix GeneralLinearGroup
variable {k : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
open BruhatTits
open Pointwise
omit [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K]
variable [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K]

theorem BruhatTits.dist_inv_isSimilar (M L M' L' : BruhatTits.Lattice R)
    (hM : Lattice.IsSimilar R M M') (hL : Lattice.IsSimilar R L L') : dist M L = dist M' L' := by sorry
