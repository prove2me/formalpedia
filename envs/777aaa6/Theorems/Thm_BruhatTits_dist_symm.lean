-- Prove2me | Theorems.Thm_BruhatTits_dist_symm
-- name    : BruhatTits.dist_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:47:55.939787+00:00
-- url     : https://prove2.me/theorems/2d520fc1-60ab-421c-a61c-7d71d13be815
-- title:
--   Bruhat Tits: dist symm
-- statement:
--   The distance on lattices is symmetric.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L363-L378
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L363-L378

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

theorem BruhatTits.dist_symm (M L : BruhatTits.Lattice R) :
    dist M L = dist L M := by sorry
