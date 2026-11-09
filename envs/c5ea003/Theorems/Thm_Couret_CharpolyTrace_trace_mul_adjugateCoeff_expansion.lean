-- Prove2me | Theorems.Thm_Couret_CharpolyTrace_trace_mul_adjugateCoeff_expansion
-- name    : Couret.CharpolyTrace.trace_mul_adjugateCoeff_expansion
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:04:16.873081+00:00
-- url     : https://prove2.me/theorems/6eaa5a46-1078-44bd-967a-2d118901e4d4
-- title:
--   Trace expansion of an adjugate coefficient product
-- statement:
--   Let $A$ be a square matrix indexed by a finite set over a commutative ring $R$. Put $p_A(X)=\det(I-XA)=\sum_{j\ge0}c_jX^j$, let $J_A(X)=\operatorname{adj}(I-XA)$, and let $B_k$ be its matrix coefficient at degree $k$. For every $k\in\mathbb N$,
--
--   $$\operatorname{tr}(AB_k)=\operatorname{tr}(A^{k+1})+\sum_{j=1}^k c_j\operatorname{tr}(A^{k+1-j}).$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyCharpolyTrace.lean#L82-L93, lines 82–93; source file SHA-256 9d047dab2b170c5e9f2aa123bbdc1e6c99a3007f1937dea965a61d17a484ce92; theorem Couret.CharpolyTrace.trace_mul_adjugateCoeff_expansion

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Theorems.Thm_Couret_CharpolyTrace_adjugateCoeff_expansion
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

theorem trace_mul_adjugateCoeff_expansion (A : Matrix i i R) (k : ℕ) :
    Matrix.trace (A * adjugateCoeff A k) = Matrix.trace (A ^ (k + 1)) +
      ∑ j ∈ Finset.range k,
        A.charpolyRev.coeff (j + 1) * Matrix.trace (A ^ (k + 1 - (j + 1))) := by sorry








end Couret.CharpolyTrace
