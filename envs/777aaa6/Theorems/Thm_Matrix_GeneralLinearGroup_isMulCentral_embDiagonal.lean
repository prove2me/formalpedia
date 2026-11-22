-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_isMulCentral_embDiagonal
-- name    : Matrix.GeneralLinearGroup.isMulCentral_embDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:52:03.395767+00:00
-- url     : https://prove2.me/theorems/ec162361-7423-4924-adb4-3f840d16a03f
-- title:
--   General Linear Group: is Mul Central emb Diagonal
-- statement:
--   The General Linear Group construction uses the is Mul Central emb Diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L575-L578
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L575-L578

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

theorem Matrix.GeneralLinearGroup.isMulCentral_embDiagonal {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : Rˣ) :
    IsMulCentral (Matrix.GeneralLinearGroup.embDiagonal R ι u) := by sorry
