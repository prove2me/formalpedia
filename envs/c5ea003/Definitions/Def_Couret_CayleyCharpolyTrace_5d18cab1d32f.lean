-- Prove2me | Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
-- name    : Couret_CayleyCharpolyTrace_5d18cab1d32f
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:14.958191+00:00
-- url     : https://prove2.me/theorems/391eb4c3-dbbd-4273-8540-4a21d8920fd4
-- title:
--   Reverse characteristic matrix and adjugate coefficients
-- statement:
--   Let $R$ be a commutative ring and $A$ a square matrix on a finite index type with decidable equality. Define the polynomial matrix $$M_A(X)=I-XA$$ after mapping entries into $R[X]$. Its adjugate-coefficient matrix $B_k(A)$ is the coefficient of $X^k$ after transporting $\operatorname{adj}(M_A)$ to a polynomial with matrix coefficients. The natural index $k$ includes zero, and the finite matrix index may be empty. These two constructions provide the algebraic objects used to relate characteristic coefficients to power traces without assuming diagonalizability or an algebraic closure.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyCharpolyTrace.lean; source file SHA-256 9d047dab2b170c5e9f2aa123bbdc1e6c99a3007f1937dea965a61d17a484ce92

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

def reverseCharmatrix (A : Matrix i i R) : Matrix i i R[X] :=
  1 - (X : R[X]) • A.map C

def adjugateCoeff (A : Matrix i i R) (k : ℕ) : Matrix i i R :=
  (matPolyEquiv (reverseCharmatrix A).adjugate).coeff k





















end Couret.CharpolyTrace


