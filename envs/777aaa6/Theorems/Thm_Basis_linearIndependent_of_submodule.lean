-- Prove2me | Theorems.Thm_Basis_linearIndependent_of_submodule
-- name    : Basis.linearIndependent_of_submodule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:41:31.048586+00:00
-- url     : https://prove2.me/theorems/b82216a5-f4a8-4cd1-a3d9-d7e647dbf28b
-- title:
--   Basis: linear Independent of submodule
-- statement:
--   The Basis construction uses the linear Independent of submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Subring.lean#L48-L53
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Subring.lean#L48-L53

import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Basis.Submodule
import Definitions.Def_BruhatTits_Utils_Subring
set_option autoImplicit false
universe uCompat vCompat wCompat
variable {ι : Type*} [DecidableEq ι]
variable {R : Type*} [Ring R]
variable {A : Subring R}
omit [DecidableEq ι]
variable {K : Type*} [Field K]
variable {R : Subring K} [IsFractionRing R K]

theorem Basis.linearIndependent_of_submodule {κ : Type*} {M : Submodule R (ι → K)} (b : Basis κ R M) :
    LinearIndependent K (fun i ↦ (b i).val) := by sorry
