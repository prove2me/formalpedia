-- Prove2me | solution 1 for QuaternionicConcurrence.State.hopfFunctional_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T21:46:17.885577+00:00
-- url     : https://prove2.me/submissions/cef41ab7-dbdf-4a11-b504-143f0eea32e9

import Mathlib
import Definitions.Def_Geometry_QuaternionicConcurrence
open Complex ComplexConjugate QuaternionicConcurrence QuaternionicConcurrence.State in
theorem solution (ψ : State) (hnorm : ψ.normSq = 1) :
    ψ.hopfFunctional = 1 ↔
      ψ.rowInner = 0 ∧ ψ.firstRowNormSq = 1 / 2 ∧ ψ.secondRowNormSq = 1 / 2 := by
  -- Lagrange identity: `|det|² + |⟨r₁, r₂⟩|² = ‖r₁‖² ‖r₂‖²`
  have hlag : Complex.normSq ψ.determinant + Complex.normSq ψ.rowInner
      = ψ.firstRowNormSq * ψ.secondRowNormSq := by
    simp only [QuaternionicConcurrence.State.determinant, QuaternionicConcurrence.State.rowInner,
      QuaternionicConcurrence.State.firstRowNormSq, QuaternionicConcurrence.State.secondRowNormSq,
      Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
    ring
  have hsum : ψ.firstRowNormSq + ψ.secondRowNormSq = 1 := by
    rw [← hnorm]
    simp only [QuaternionicConcurrence.State.normSq, QuaternionicConcurrence.State.firstRowNormSq,
      QuaternionicConcurrence.State.secondRowNormSq]
    ring
  have hhopf : ψ.hopfFunctional = 2 * ‖ψ.determinant‖ := by
    unfold QuaternionicConcurrence.State.hopfFunctional
    rw [hnorm, if_neg one_ne_zero, div_one]
  have hnd : ‖ψ.determinant‖ ^ 2 = Complex.normSq ψ.determinant :=
    (Complex.normSq_eq_norm_sq _).symm
  have hn1 : 0 ≤ ψ.firstRowNormSq := by
    unfold QuaternionicConcurrence.State.firstRowNormSq
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hn2 : 0 ≤ ψ.secondRowNormSq := by
    unfold QuaternionicConcurrence.State.secondRowNormSq
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hin : 0 ≤ Complex.normSq ψ.rowInner := Complex.normSq_nonneg _
  rw [hhopf]
  constructor
  · intro h
    have hd : ‖ψ.determinant‖ = 1 / 2 := by linarith
    have hdsq : Complex.normSq ψ.determinant = 1 / 4 := by
      rw [← hnd, hd]
      norm_num
    -- AM–GM: `‖r₁‖² ‖r₂‖² ≤ 1/4`, with equality only for equal norms
    have hamgm : ψ.firstRowNormSq * ψ.secondRowNormSq ≤ 1 / 4 := by
      nlinarith [sq_nonneg (ψ.firstRowNormSq - ψ.secondRowNormSq)]
    have hinner0 : Complex.normSq ψ.rowInner = 0 := by linarith
    have hprod : ψ.firstRowNormSq * ψ.secondRowNormSq = 1 / 4 := by linarith
    have hsq : (ψ.firstRowNormSq - ψ.secondRowNormSq) ^ 2 = 0 := by nlinarith
    have heq : ψ.firstRowNormSq = ψ.secondRowNormSq := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
      linarith
    exact ⟨Complex.normSq_eq_zero.1 hinner0, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2⟩
    rw [h0, h1, h2, map_zero] at hlag
    have hdsq : ‖ψ.determinant‖ ^ 2 = (1 / 2) ^ 2 := by
      rw [hnd]
      linarith
    have hd : ‖ψ.determinant‖ = 1 / 2 :=
      (pow_left_inj₀ (norm_nonneg _) (by norm_num) two_ne_zero).1 hdsq
    rw [hd]
    norm_num
