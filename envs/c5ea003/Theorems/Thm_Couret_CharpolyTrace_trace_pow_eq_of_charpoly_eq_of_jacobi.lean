-- Prove2me | Theorems.Thm_Couret_CharpolyTrace_trace_pow_eq_of_charpoly_eq_of_jacobi
-- name    : Couret.CharpolyTrace.trace_pow_eq_of_charpoly_eq_of_jacobi
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:20:53.361528+00:00
-- url     : https://prove2.me/theorems/fe36edcd-d50e-4fb4-80c9-0ee07b49d18a
-- title:
--   Equal characteristic polynomials give equal power traces under Jacobi identities
-- statement:
--   Let $A,B$ be square matrices with the same finite index set over a commutative ring. Suppose they have equal characteristic polynomials and each satisfies the reverse characteristic Jacobi identity $\frac{d}{dX}\det(I-XA)=-\operatorname{tr}(A\operatorname{adj}(I-XA))$, and similarly for B. Then
--
--   $$\operatorname{tr}(A^k)=\operatorname{tr}(B^k)\qquad(k\in\mathbb N).$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyCharpolyTrace.lean#L107-L137, lines 107–137; source file SHA-256 9d047dab2b170c5e9f2aa123bbdc1e6c99a3007f1937dea965a61d17a484ce92; theorem Couret.CharpolyTrace.trace_pow_eq_of_charpoly_eq_of_jacobi

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Theorems.Thm_Couret_CharpolyTrace_trace_mul_adjugateCoeff_eq_of_jacobi
import Theorems.Thm_Couret_CharpolyTrace_trace_mul_adjugateCoeff_expansion
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

theorem trace_pow_eq_of_charpoly_eq_of_jacobi
    (A B : Matrix i i R) (hp : A.charpoly = B.charpoly)
    (hJA : Polynomial.derivative A.charpolyRev =
      -Matrix.trace (A.map C * (reverseCharmatrix A).adjugate))
    (hJB : Polynomial.derivative B.charpolyRev =
      -Matrix.trace (B.map C * (reverseCharmatrix B).adjugate))
    (k : ℕ) : Matrix.trace (A ^ k) = Matrix.trace (B ^ k) := by sorry




end Couret.CharpolyTrace
