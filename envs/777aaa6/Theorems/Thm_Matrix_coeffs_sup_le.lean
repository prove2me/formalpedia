-- Prove2me | Theorems.Thm_Matrix_coeffs_sup_le
-- name    : Matrix.coeffs_sup_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:50:25.357171+00:00
-- url     : https://prove2.me/theorems/cf809b6d-1bbe-41cc-aa2e-317821b56c3b
-- title:
--   Matrix: coeffs sup le
-- statement:
--   The Matrix construction uses the coeffs sup le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L157-L164
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L157-L164

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

theorem Matrix.coeffs_sup_le {g : Matrix n m R} {a : Γ₀}
    (h : ∀ (i : n) (j : m), v (g i j) ≤ a) :
    g.coeffs_sup v ≤ a := by sorry
