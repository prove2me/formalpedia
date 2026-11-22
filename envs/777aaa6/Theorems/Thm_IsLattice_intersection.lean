-- Prove2me | Theorems.Thm_IsLattice_intersection
-- name    : IsLattice.intersection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:58:18.392753+00:00
-- url     : https://prove2.me/theorems/13674788-9575-4fef-9733-581ac147091f
-- title:
--   Is Lattice: intersection
-- statement:
--   The intersection of two lattices is a lattice.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Basic.lean#L300-L315
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Basic.lean#L300-L315

import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.Algebra.Group.Action.Pointwise.Set.Finite
import Definitions.Def_BruhatTits_Lattice_Basic
set_option autoImplicit false
variable {K : Type*} [Field K] {R : Subring K}
open Pointwise
variable {ι : Type*}
variable [IsFractionRing R K]
variable [IsPrincipalIdealRing R] (M : Submodule R (ι → K)) [IsLattice M]
variable [Fintype ι]

theorem IsLattice.intersection (M N : Submodule R (ι → K)) [IsLattice M] [IsLattice N] :
    IsLattice (M ⊓ N) := by sorry
