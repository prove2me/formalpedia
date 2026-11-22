-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_diagonal_smul
-- name    : Matrix.GeneralLinearGroup.diagonal_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:50:35.442389+00:00
-- url     : https://prove2.me/theorems/40bf3778-1e6e-4dba-a37b-9277d560d65c
-- title:
--   General Linear Group: diagonal smul
-- statement:
--   The General Linear Group construction uses the diagonal smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L497-L504
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L497-L504

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
open Pointwise

theorem Matrix.GeneralLinearGroup.diagonal_smul (f : ι → Kˣ) (M : Submodule R (ι → K)) (hf : ∀ i j, f i = f j) (i : ι) :
    GL.diagonal f • M = f i • M := by sorry
