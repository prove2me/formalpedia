-- Prove2me | Theorems.Thm_Matrix_coeffs_sup_fromBlocks
-- name    : Matrix.coeffs_sup_fromBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:51:35.929662+00:00
-- url     : https://prove2.me/theorems/83e4d332-0ed1-4768-a758-4447581f9add
-- title:
--   Matrix: coeffs sup from Blocks
-- statement:
--   The Matrix construction uses the coeffs sup from Blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L191-L200
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L191-L200

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
variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
variable [Finite n] [Finite m] [Finite n'] [Finite m'] [Nonempty n] [Nonempty m]
  [Nonempty n'] [Nonempty m']

theorem Matrix.coeffs_sup_fromBlocks (A : Matrix n n' R) (B : Matrix n m R)
    (C : Matrix m' n' R) (D : Matrix m' m R) :
    (A.fromBlocks B C D).coeffs_sup v =
      A.coeffs_sup v ⊔ B.coeffs_sup v ⊔ C.coeffs_sup v ⊔ D.coeffs_sup v := by sorry
