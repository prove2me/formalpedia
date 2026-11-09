-- Prove2me | Theorems.Thm_Couret_CharpolyTrace_trace_pow_eq_of_charpoly_eq
-- name    : Couret.CharpolyTrace.trace_pow_eq_of_charpoly_eq
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:31:14.516204+00:00
-- url     : https://prove2.me/theorems/841afd25-c0b1-4c38-840e-a94b1195e0c3
-- title:
--   Characteristic polynomial equality determines all power traces
-- statement:
--   Let $A,B$ be square matrices with the same finite index set over any commutative ring. If their characteristic polynomials agree, then
--
--   $$\operatorname{tr}(A^k)=\operatorname{tr}(B^k)\qquad(k\in\mathbb N).$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyCharpolyTrace.lean#L139-L149, lines 139–149; source file SHA-256 9d047dab2b170c5e9f2aa123bbdc1e6c99a3007f1937dea965a61d17a484ce92; theorem Couret.CharpolyTrace.trace_pow_eq_of_charpoly_eq

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Theorems.Thm_Couret_CharpolyTrace_trace_pow_eq_of_charpoly_eq_of_jacobi
import Theorems.Thm_Matrix_derivative_det_one_sub_X_smul
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.Abel

/-!
Algebraic bridge from characteristic polynomials to power traces.
This development uses the coefficients of the adjugate of `1 - X A`.
It does not use diagonalizability or an algebraic closure.
-/

noncomputable section

open Polynomial Matrix
open scoped BigOperators

namespace Couret.CharpolyTrace

variable {R : Type*} [CommRing R]
variable {i : Type*} [Fintype i] [DecidableEq i]

theorem trace_pow_eq_of_charpoly_eq
    (A B : Matrix i i R) (hp : A.charpoly = B.charpoly)
    (k : ℕ) : Matrix.trace (A ^ k) = Matrix.trace (B ^ k) := by sorry


end Couret.CharpolyTrace
