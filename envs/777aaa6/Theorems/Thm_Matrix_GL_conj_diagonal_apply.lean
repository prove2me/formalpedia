-- Prove2me | Theorems.Thm_Matrix_GL_conj_diagonal_apply
-- name    : Matrix.GL.conj_diagonal_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:49:11.39402+00:00
-- url     : https://prove2.me/theorems/71f2345c-457f-488f-838f-e1f5f54213ac
-- title:
--   GL: conj diagonal apply
-- statement:
--   The GL construction uses the conj diagonal apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L355-L366
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L355-L366

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

theorem Matrix.GL.conj_diagonal_apply {ι : Type*} [Fintype ι]
    [DecidableEq ι] (d : ι → Rˣ) (g : GL ι R) (i j : ι) :
    MulAut.conj (Matrix.GL.diagonal d) g i j = (d i) * (d j)⁻¹ * g i j := by sorry
