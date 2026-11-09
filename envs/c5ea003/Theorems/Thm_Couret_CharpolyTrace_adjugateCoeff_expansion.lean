-- Prove2me | Theorems.Thm_Couret_CharpolyTrace_adjugateCoeff_expansion
-- name    : Couret.CharpolyTrace.adjugateCoeff_expansion
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:57:13.540629+00:00
-- url     : https://prove2.me/theorems/e1caa1bd-b11d-4c27-96c3-02e10bc41507
-- title:
--   Explicit expansion of the adjugate coefficients
-- statement:
--   Let $A$ be a square matrix indexed by a finite set over a commutative ring $R$. Put $p_A(X)=\det(I-XA)=\sum_{j\ge0}c_jX^j$, let $J_A(X)=\operatorname{adj}(I-XA)$, and let $B_k$ be its matrix coefficient at degree $k$. For every $k\in\mathbb N$,
--
--   $$B_k=A^k+\sum_{j=1}^k c_jA^{k-j}.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyCharpolyTrace.lean#L59-L80, lines 59–80; source file SHA-256 9d047dab2b170c5e9f2aa123bbdc1e6c99a3007f1937dea965a61d17a484ce92; theorem Couret.CharpolyTrace.adjugateCoeff_expansion

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

theorem adjugateCoeff_expansion (A : Matrix i i R) (k : ℕ) :
    adjugateCoeff A k = A ^ k +
      ∑ j ∈ Finset.range k,
        A.charpolyRev.coeff (j + 1) • A ^ (k - (j + 1)) := by sorry










end Couret.CharpolyTrace
