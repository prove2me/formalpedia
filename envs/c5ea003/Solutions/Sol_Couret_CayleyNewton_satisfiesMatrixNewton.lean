-- Prove2me | solution 1 for Couret.CayleyNewton.satisfiesMatrixNewton
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:19:28.991763+00:00
-- url     : https://prove2.me/submissions/ee3c9f9d-9692-4ed4-87d1-bca370b75974

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

theorem reverseCharpolyCoeff_eq_charpolyRev
    (A : Matrix i i ℚ) (k : ℕ) :
    reverseCharpolyCoeff A k = A.charpolyRev.coeff k := by
  rw [reverseCharpolyCoeff, ← Matrix.reverse_charpoly,
    Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim]
  by_cases hk : k ≤ Fintype.card i
  · rw [if_pos hk, Polynomial.revAt_le hk]
  · have hlt : Fintype.card i < k := Nat.lt_of_not_ge hk
    have hdeg : A.charpoly.natDegree < k := by
      simpa only [Matrix.charpoly_natDegree_eq_dim] using hlt
    rw [if_neg hk, Polynomial.revAt_eq_self_of_lt hlt,
      Polynomial.coeff_eq_zero_of_natDegree_lt hdeg]

/-- Every rational square matrix satisfies the precise Newton recurrence
already specified in `CayleyTwoColourNewton`. This removes the explicit
matrix-recurrence hypothesis from that module's conditional results. -/
theorem p2m_local_satisfiesMatrixNewton (A : Matrix i i ℚ) : SatisfiesMatrixNewton A := by
  intro k hk
  cases k with
  | zero => omega
  | succ k =>
      have hJ : Polynomial.derivative A.charpolyRev =
          -Matrix.trace (A.map C * (Couret.CharpolyTrace.reverseCharmatrix A).adjugate) := by
        simpa only [Matrix.charpolyRev, Couret.CharpolyTrace.reverseCharmatrix] using
          Matrix.derivative_det_one_sub_X_smul A
      have h := Couret.CharpolyTrace.trace_mul_adjugateCoeff_eq_of_jacobi A hJ k
      rw [Couret.CharpolyTrace.trace_mul_adjugateCoeff_expansion] at h
      unfold NewtonTraceEquation
      simp only [reverseCharpolyCoeff_eq_charpolyRev, Nat.add_sub_cancel]
      simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using
        (eq_neg_iff_add_eq_zero.mp h)



end Couret.CayleyNewton


universe p2m_u_0
theorem solution : ∀ {i : Type p2m_u_0} [inst : Fintype.{p2m_u_0} i] [inst_1 : DecidableEq.{p2m_u_0 + 1} i]
  (A : Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat), @Couret.CayleyNewton.SatisfiesMatrixNewton.{p2m_u_0} i inst inst_1 A := @_root_.Couret.CayleyNewton.p2m_local_satisfiesMatrixNewton

