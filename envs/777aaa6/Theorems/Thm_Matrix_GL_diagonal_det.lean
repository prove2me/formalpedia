-- Prove2me | Theorems.Thm_Matrix_GL_diagonal_det
-- name    : Matrix.GL.diagonal_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:51:50.100047+00:00
-- url     : https://prove2.me/theorems/cb58a101-a33c-4374-baf3-97772d373c46
-- title:
--   GL: diagonal det
-- statement:
--   The GL construction uses the diagonal det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L330-L333
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L330-L333

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

theorem Matrix.GL.diagonal_det (g : n → Rˣ) :
    GeneralLinearGroup.det (GL.diagonal g) = ∏ i : n, g i := by sorry
