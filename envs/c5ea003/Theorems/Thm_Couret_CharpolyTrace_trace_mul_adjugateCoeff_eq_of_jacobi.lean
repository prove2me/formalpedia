-- Prove2me | Theorems.Thm_Couret_CharpolyTrace_trace_mul_adjugateCoeff_eq_of_jacobi
-- name    : Couret.CharpolyTrace.trace_mul_adjugateCoeff_eq_of_jacobi
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:04:20.581201+00:00
-- url     : https://prove2.me/theorems/0e2e54f1-ea0d-4290-a231-a17f99e0a26f
-- title:
--   Jacobi derivative yields a coefficient trace identity
-- statement:
--   Let $A$ be a square matrix indexed by a finite set over a commutative ring $R$. Put $p_A(X)=\det(I-XA)=\sum_{j\ge0}c_jX^j$, let $J_A(X)=\operatorname{adj}(I-XA)$, and let $B_k$ be its matrix coefficient at degree $k$. Assume $p_A\prime(X)=-\operatorname{tr}(AJ_A(X))$. Then for every $k\in\mathbb N$,
--
--   $$\operatorname{tr}(AB_k)=-(k+1)c_{k+1},$$
--
--   with the integer factor interpreted in $R$.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyCharpolyTrace.lean#L95-L105, lines 95–105; source file SHA-256 9d047dab2b170c5e9f2aa123bbdc1e6c99a3007f1937dea965a61d17a484ce92; theorem Couret.CharpolyTrace.trace_mul_adjugateCoeff_eq_of_jacobi

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
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

theorem trace_mul_adjugateCoeff_eq_of_jacobi (A : Matrix i i R)
    (hJ : Polynomial.derivative A.charpolyRev =
      -Matrix.trace (A.map C * (reverseCharmatrix A).adjugate)) (k : ℕ) :
    Matrix.trace (A * adjugateCoeff A k) =
      -(A.charpolyRev.coeff (k + 1) * ((k : R) + 1)) := by sorry






end Couret.CharpolyTrace
