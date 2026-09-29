-- Prove2me | solution 1 for QuaternionicConcurrence.State.hopfFunctional_mem_unitInterval
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:19:55.007689+00:00
-- url     : https://prove2.me/submissions/340ff0b9-d8f9-49e9-a704-579b263dfe00

-- Sol generated from Geometry/QuaternionicConcurrence.lean
import Mathlib
import Definitions.Def_Geometry_QuaternionicConcurrence

/-!
# Quaternionic Hopf concurrence and its sharp maximizers

A two-qubit vector is a pair of complex rows.  Its quaternionic Hopf
coordinate has a distinguished complex component, the determinant.  This file
uses its canonically normalized modulus as a real-valued functional and proves
a rigid equality classification: on the unit sphere it is one exactly when
the coefficient rows are orthogonal and have equal squared norm.
-/

open Complex ComplexConjugate

noncomputable section

open QuaternionicConcurrence


open State







/-- The two-dimensional complex Lagrange identity.  It identifies determinant
magnitude with the part of one row orthogonal to the other. -/
theorem lagrange_identity (ψ : State) :
    Complex.normSq ψ.determinant + Complex.normSq ψ.rowInner =
      ψ.firstRowNormSq * ψ.secondRowNormSq := by
  simp [determinant, rowInner, firstRowNormSq, secondRowNormSq, Complex.normSq_add,
    Complex.normSq_sub, Complex.normSq_mul, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring






open QuaternionicConcurrence.State in
theorem solution(ψ : State) (hnorm : ψ.normSq = 1) :
    0 ≤ ψ.hopfFunctional ∧ ψ.hopfFunctional ≤ 1 := by
  unfold hopfFunctional
  simp [hnorm]
  -- Need to prove 2 * ‖ψ.determinant‖ ≤ 1
  -- Using Lagrange identity: ‖determinant‖² + ‖rowInner‖² = firstRowNormSq * secondRowNormSq
  -- So ‖determinant‖² ≤ firstRowNormSq * secondRowNormSq
  -- And firstRowNormSq + secondRowNormSq = normSq = 1
  -- By AM-GM: firstRowNormSq * secondRowNormSq ≤ 1/4
  have h1 : ψ.firstRowNormSq + ψ.secondRowNormSq = 1 := by
    unfold State.firstRowNormSq State.secondRowNormSq
    simp only [State.normSq] at hnorm
    linarith
  -- Use Lagrange identity
  have h2 := lagrange_identity ψ
  -- ‖determinant‖² ≤ firstRowNormSq * secondRowNormSq
  have h3 : ‖ψ.determinant‖^2 ≤ ψ.firstRowNormSq * ψ.secondRowNormSq := by
    rw [Complex.normSq_eq_norm_sq] at h2
    linarith [Complex.normSq_nonneg ψ.rowInner]
  -- By AM-GM: firstRowNormSq * secondRowNormSq ≤ (1/2)² = 1/4
  have h4 : ψ.firstRowNormSq * ψ.secondRowNormSq ≤ 1 / 4 := by
    have := sq_nonneg (ψ.firstRowNormSq - ψ.secondRowNormSq)
    nlinarith
  -- Therefore ‖determinant‖² ≤ 1/4
  have h5 : ‖ψ.determinant‖^2 ≤ 1 / 4 := le_trans h3 h4
  -- So ‖determinant‖ ≤ 1/2
  have h6 : ‖ψ.determinant‖ ≤ 1 / 2 := by
    have := Real.sqrt_le_sqrt h5
    rw [Real.sqrt_sq (norm_nonneg _)] at this
    norm_num at this
    exact this
  linarith
