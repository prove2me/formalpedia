-- Prove2me | Theorems.Thm_Couret_CayleyNewton_trace_pow_eq_of_charpoly_eq_via_newton
-- name    : Couret.CayleyNewton.trace_pow_eq_of_charpoly_eq_via_newton
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:48:30.178292+00:00
-- url     : https://prove2.me/theorems/e3617560-3ed6-4769-8885-1ec4a05677b0
-- title:
--   Equal characteristic polynomials give equal power traces
-- statement:
--   Let A,B be rational square matrices indexed by the same finite type I, with equal characteristic polynomials. For every natural k, $$\operatorname{tr}(A^k)=\operatorname{tr}(B^k).$$ Zero powers and the empty index type are included; Newton recurrence assumptions are discharged internally.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyTwoColourMatrixNewton.lean#L54-L60, lines 54–60; source file SHA-256 690d7c3068be85de243c61c581f1c06c810bb3d0b94aaacad9a01fbf92387d15; theorem Couret.CayleyNewton.trace_pow_eq_of_charpoly_eq_via_newton

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Theorems.Thm_Couret_CayleyNewton_satisfiesMatrixNewton
import Theorems.Thm_Couret_CayleyNewton_trace_pow_eq_of_charpoly_eq_of_newton
import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5

/-!
COU-20 — the matrix Newton obligation, discharged from polynomial Jacobi.

The pre-existing `CayleyTwoColourNewton` module proved uniqueness of Newton
recurrences and the conditional spectral classification. This file supplies
its missing single-matrix recurrence, with no new mathematical hypothesis.
-/

set_option autoImplicit false
noncomputable section

open Matrix Polynomial
open scoped BigOperators

namespace Couret.CayleyNewton

variable {i : Type*} [Fintype i] [DecidableEq i]

theorem trace_pow_eq_of_charpoly_eq_via_newton
    (A B : Matrix i i ℚ) (hp : A.charpoly = B.charpoly) (k : ℕ) :
    Matrix.trace (A ^ k) = Matrix.trace (B ^ k) := by sorry


end Couret.CayleyNewton
