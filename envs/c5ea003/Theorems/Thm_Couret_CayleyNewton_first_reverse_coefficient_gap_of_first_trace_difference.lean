-- Prove2me | Theorems.Thm_Couret_CayleyNewton_first_reverse_coefficient_gap_of_first_trace_difference
-- name    : Couret.CayleyNewton.first_reverse_coefficient_gap_of_first_trace_difference
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:31:16.239563+00:00
-- url     : https://prove2.me/theorems/e76836c0-d5d2-48e0-ab99-fd43bf6e0be9
-- title:
--   A first trace discrepancy gives the first reversed coefficient discrepancy
-- statement:
--   Let $A,B$ be rational square matrices on one finite index type of size $n$, and let $k>0$. Set $c_A(j)=[X^{n-j}]\chi_A$ for $j\le n$ and zero otherwise, and similarly for $B$. If their power traces agree for every $0<j<k$ and differ at $k$, then
--
--   $$c_A(j)=c_B(j)\ (0<j<k),\quad c_A(k)\ne c_B(k),$$
--   $$k(c_A(k)-c_B(k))=-(\operatorname{tr}(A^k)-\operatorname{tr}(B^k)).$$
--
--   No Newton recurrence is assumed in this statement.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/bef25648f750d1b9d7792a883597021665e3ba00/research/correspondants_20261013/lean/CayleyTwoColourFirstCoefficient.lean#L25-L67, lines 25–67; source file SHA-256 f26de50d22cca32e5b50cae2954724a46bdbf8e8b8465f15443d7d7c8bb63e39; theorem Couret.CayleyNewton.first_reverse_coefficient_gap_of_first_trace_difference

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Theorems.Thm_Couret_CayleyNewton_newton_coefficient_prefix_eq
import Theorems.Thm_Couret_CayleyNewton_newton_first_coefficient_ne_of_trace_prefix
import Theorems.Thm_Couret_CayleyNewton_newton_first_gap_of_trace_prefix
import Theorems.Thm_Couret_CayleyNewton_satisfiesMatrixNewton
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f

/-!
COU-20 — exact first characteristic coefficient obstruction.

RESEARCH CANDIDATE: must be compiled with the pinned Lean 4.29.1
toolchain and its #print axioms checked before a certification claim.

The general matrix theorem uses the now-proposed unconditional Newton
recurrence for rational square matrices. The directed Cayley corollary
uses the previously established first trace discrepancy at one third
of the odd quotient cardinality. No graph symmetry, loop exclusion,
new axiom, or independent generation assumption is introduced.
-/

set_option autoImplicit false
noncomputable section

open Matrix

namespace Couret.CayleyNewton

variable {i : Type*} [Fintype i] [DecidableEq i]

theorem first_reverse_coefficient_gap_of_first_trace_difference
    (A B : Matrix i i ℚ) (k : ℕ) (hk : 0 < k)
    (hprev : ∀ j : ℕ, 0 < j → j < k →
      Matrix.trace (A ^ j) = Matrix.trace (B ^ j))
    (hdiff : Matrix.trace (A ^ k) ≠ Matrix.trace (B ^ k)) :
    (∀ j : ℕ, 0 < j → j < k →
        reverseCharpolyCoeff A j = reverseCharpolyCoeff B j) ∧
      reverseCharpolyCoeff A k ≠ reverseCharpolyCoeff B k ∧
      (k : ℚ) * (reverseCharpolyCoeff A k - reverseCharpolyCoeff B k) =
        -(Matrix.trace (A ^ k) - Matrix.trace (B ^ k)) := by sorry


end Couret.CayleyNewton

namespace Couret.CayleyDoublet

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]



end Couret.CayleyDoublet
