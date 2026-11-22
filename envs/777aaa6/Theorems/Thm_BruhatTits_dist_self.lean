-- Prove2me | Theorems.Thm_BruhatTits_dist_self
-- name    : BruhatTits.dist_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:47:54.050195+00:00
-- url     : https://prove2.me/theorems/6d90ad0c-2c6d-4667-a367-117b60bd25ba
-- title:
--   Bruhat Tits: dist self
-- statement:
--   The distance of a lattice to itself is zero.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L382-L387
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L382-L387

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

theorem BruhatTits.dist_self (L : BruhatTits.Lattice R) :
    dist L L = 0 := by sorry
