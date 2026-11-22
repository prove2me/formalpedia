-- Prove2me | Theorems.Thm_BruhatTits_dist_smul_eq_dist
-- name    : BruhatTits.dist_smul_eq_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:48:42.000179+00:00
-- url     : https://prove2.me/theorems/4caf47f3-7b1b-45ca-9da2-0d1a46657607
-- title:
--   Bruhat Tits: dist smul eq dist
-- statement:
--   The distance of a lattice `M` to a given lattice `L` does not change when `M` is scaled
--   by some `a : Kˣ`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L448-L480
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L448-L480

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

theorem BruhatTits.dist_smul_eq_dist (M L : BruhatTits.Lattice R) (a : Kˣ) :
    dist (a • M) L = dist M L := by sorry
