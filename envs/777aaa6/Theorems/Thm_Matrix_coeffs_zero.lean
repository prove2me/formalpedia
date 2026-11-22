-- Prove2me | Theorems.Thm_Matrix_coeffs_zero
-- name    : Matrix.coeffs_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:50:59.671005+00:00
-- url     : https://prove2.me/theorems/0cabe7f0-68d1-490b-b1f6-9967b359eacb
-- title:
--   Matrix: coeffs zero
-- statement:
--   The Matrix construction uses the coeffs zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L72-L77
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L72-L77

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

theorem Matrix.coeffs_zero [Zero R] [Nonempty n] [Nonempty m] : (0 : Matrix n m R).coeffs = {0} := by sorry
