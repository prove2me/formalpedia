-- Prove2me | Theorems.Thm_Matrix_GL_isMulCentral_diagonal
-- name    : Matrix.GL.isMulCentral_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:50:08.999879+00:00
-- url     : https://prove2.me/theorems/9db56017-ec3d-4d7d-bf4c-a944b379e5d5
-- title:
--   GL: is Mul Central diagonal
-- statement:
--   The GL construction uses the is Mul Central diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L368-L376
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L368-L376

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

theorem Matrix.GL.isMulCentral_diagonal {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : Rˣ) :
    IsMulCentral (Matrix.GL.diagonal fun _ : ι ↦ a) := by sorry
