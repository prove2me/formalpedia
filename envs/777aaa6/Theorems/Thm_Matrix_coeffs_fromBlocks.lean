-- Prove2me | Theorems.Thm_Matrix_coeffs_fromBlocks
-- name    : Matrix.coeffs_fromBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:50:57.104039+00:00
-- url     : https://prove2.me/theorems/f7427fd8-625d-4874-a434-8214a7bfec29
-- title:
--   Matrix: coeffs from Blocks
-- statement:
--   The Matrix construction uses the coeffs from Blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L62-L70
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L62-L70

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

theorem Matrix.coeffs_fromBlocks (A : Matrix n n' R) (B : Matrix n m R) (C : Matrix m' n' R)
    (D : Matrix m' m R) :
    (A.fromBlocks B C D).coeffs =
        A.coeffs ∪ B.coeffs ∪ C.coeffs ∪ D.coeffs := by sorry
