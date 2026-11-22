-- Prove2me | Theorems.Thm_Basis_toGL_toSubmodule
-- name    : Basis.toGL_toSubmodule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:57:07.565557+00:00
-- url     : https://prove2.me/theorems/ea7f3048-9efc-4143-9101-8f650a6d3ae2
-- title:
--   Basis: to GL to Submodule
-- statement:
--   The Basis construction uses the to GL to Submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Basic.lean#L175-L207
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Basic.lean#L175-L207

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
open Basis
variable [Fintype ι] [DecidableEq ι]

theorem Basis.toGL_toSubmodule {M : Submodule R (ι → K)} [IsLattice M] (b : Basis ι R M) :
    (Basis.toGL b).toSubmodule = M := by sorry
