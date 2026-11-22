-- Prove2me | Theorems.Thm_Matrix_coeffs_sup_at_sup
-- name    : Matrix.coeffs_sup_at_sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:49:26.534562+00:00
-- url     : https://prove2.me/theorems/e9be5eaa-a47a-4b93-8bda-7fd2403013a5
-- title:
--   Matrix: coeffs sup at sup
-- statement:
--   The Matrix construction uses the coeffs sup at sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L182-L184
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L182-L184

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

theorem Matrix.coeffs_sup_at_sup (g : Matrix n m R) :
    v (g (g.coeffs_sup_at v).1 (g.coeffs_sup_at v).2) = g.coeffs_sup v := by sorry
