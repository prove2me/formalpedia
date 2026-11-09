-- Prove2me | Theorems.Thm_Couret_CayleyNewton_satisfiesMatrixNewton
-- name    : Couret.CayleyNewton.satisfiesMatrixNewton
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:19:24.287234+00:00
-- url     : https://prove2.me/theorems/c220eec4-2d66-4cf1-a385-384227eecf28
-- title:
--   Every rational matrix satisfies the specified Newton recurrence
-- statement:
--   Let A be a rational square matrix on a finite index type I. Write c_j(A) for reverse characteristic coefficients and u_j=tr(A^j). Then for every k>0, $$u_k+\sum_{j=1}^{k-1}c_j(A)u_{k-j}+kc_k(A)=0.$$ The index type may be empty; no additional recurrence hypothesis is assumed.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyTwoColourMatrixNewton.lean#L35-L52, lines 35–52; source file SHA-256 690d7c3068be85de243c61c581f1c06c810bb3d0b94aaacad9a01fbf92387d15; theorem Couret.CayleyNewton.satisfiesMatrixNewton

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Theorems.Thm_Couret_CharpolyTrace_trace_mul_adjugateCoeff_eq_of_jacobi
import Theorems.Thm_Couret_CharpolyTrace_trace_mul_adjugateCoeff_expansion
import Theorems.Thm_Matrix_derivative_det_one_sub_X_smul
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

theorem satisfiesMatrixNewton (A : Matrix i i ℚ) : SatisfiesMatrixNewton A := by sorry




end Couret.CayleyNewton
