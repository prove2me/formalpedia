-- Prove2me | Theorems.Thm_Matrix_coeffs_sup_zero
-- name    : Matrix.coeffs_sup_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:51:39.814479+00:00
-- url     : https://prove2.me/theorems/3b2cb681-e7c0-46da-8988-c5705a25f64a
-- title:
--   Matrix: coeffs sup zero
-- statement:
--   The Matrix construction uses the coeffs sup zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L278-L279
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L278-L279

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
variable [DecidableEq m] [Fintype n] [Fintype m]
variable [Fintype n'] [Nonempty n'] [Fintype m'] [Nonempty m']
variable [DecidableEq n'] [DecidableEq m']
variable [Nonempty n] [Nonempty m]
omit [DecidableEq m]

theorem Matrix.coeffs_sup_zero : (0 : Matrix n m R).coeffs_sup v = 0 := by sorry
