-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_mem_smul
-- name    : Matrix.GeneralLinearGroup.mem_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:49:15.96072+00:00
-- url     : https://prove2.me/theorems/72d83047-5b0e-463b-b709-cafb4f74972f
-- title:
--   General Linear Group: mem smul
-- statement:
--   The General Linear Group construction uses the mem smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L491-L494
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L491-L494

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Subring
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Block
import Definitions.Def_BruhatTits_Utils_Matrix
set_option autoImplicit false
open BigOperators
open Matrix
variable {R : Type*}
variable {n m n' m' : Type*}
variable [CommRing R]
variable [DecidableEq n] [Fintype n]
variable [DecidableEq m] [Fintype m]
open Matrix.GeneralLinearGroup
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {K : Type*} [CommRing K]
variable {R : Subring K}

theorem Matrix.GeneralLinearGroup.mem_smul (g : GL ι K) (M : Submodule R (ι → K)) (x : ι → K) :
    x ∈ g • M ↔ ∃ y ∈ M, g.val *ᵥ y = x := by sorry
