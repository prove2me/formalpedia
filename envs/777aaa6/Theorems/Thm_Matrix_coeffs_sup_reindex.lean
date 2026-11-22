-- Prove2me | Theorems.Thm_Matrix_coeffs_sup_reindex
-- name    : Matrix.coeffs_sup_reindex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:51:39.806727+00:00
-- url     : https://prove2.me/theorems/7fb6dc63-1d09-4356-9981-79f9c8aee26c
-- title:
--   Matrix: coeffs sup reindex
-- statement:
--   The Matrix construction uses the coeffs sup reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L264-L266
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L264-L266

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
omit [DecidableEq m] [DecidableEq n'] [DecidableEq m']

theorem Matrix.coeffs_sup_reindex [Nonempty n] [Nonempty m] (g : Matrix n m R) (e : n ≃ n') (f : m ≃ m') :
    (reindex e f g).coeffs_sup v = g.coeffs_sup v := by sorry
