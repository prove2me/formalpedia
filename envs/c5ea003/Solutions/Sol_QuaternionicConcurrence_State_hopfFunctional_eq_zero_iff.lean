-- Prove2me | solution 1 for QuaternionicConcurrence.State.hopfFunctional_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:36:19.683977+00:00
-- url     : https://prove2.me/submissions/7a804371-8339-4444-88d2-ee299a96034f

import Mathlib
import Definitions.Def_Geometry_QuaternionicConcurrence

noncomputable section
open QuaternionicConcurrence State

theorem solution (ψ : State) : ψ.hopfFunctional = 0 ↔ ψ.determinant = 0 := by
  unfold hopfFunctional
  split_ifs with h0
  · constructor
    · intro _
      have hsum : Complex.normSq ψ.a + Complex.normSq ψ.b + Complex.normSq ψ.c + Complex.normSq ψ.d = 0 := by
        simpa [State.normSq] using h0
      have ha0 : Complex.normSq ψ.a = 0 := by
        have := Complex.normSq_nonneg ψ.a
        have := Complex.normSq_nonneg ψ.b
        have := Complex.normSq_nonneg ψ.c
        have := Complex.normSq_nonneg ψ.d
        nlinarith
      have hb0 : Complex.normSq ψ.b = 0 := by
        have := Complex.normSq_nonneg ψ.a
        have := Complex.normSq_nonneg ψ.b
        have := Complex.normSq_nonneg ψ.c
        have := Complex.normSq_nonneg ψ.d
        nlinarith
      have hc0 : Complex.normSq ψ.c = 0 := by
        have := Complex.normSq_nonneg ψ.a
        have := Complex.normSq_nonneg ψ.b
        have := Complex.normSq_nonneg ψ.c
        have := Complex.normSq_nonneg ψ.d
        nlinarith
      have hd0 : Complex.normSq ψ.d = 0 := by
        have := Complex.normSq_nonneg ψ.a
        have := Complex.normSq_nonneg ψ.b
        have := Complex.normSq_nonneg ψ.c
        have := Complex.normSq_nonneg ψ.d
        nlinarith
      have ea := Complex.normSq_eq_zero.mp ha0
      have eb := Complex.normSq_eq_zero.mp hb0
      have ec := Complex.normSq_eq_zero.mp hc0
      have ed := Complex.normSq_eq_zero.mp hd0
      simp [determinant, ea, eb, ec, ed]
    · intro; rfl
  · constructor
    · intro h
      have hdiv : 2 * ‖ψ.determinant‖ / ψ.normSq = 0 := h
      have hnum : 2 * ‖ψ.determinant‖ = 0 := (div_eq_zero_iff.mp hdiv).resolve_right h0
      have : ‖ψ.determinant‖ = 0 := by nlinarith
      exact norm_eq_zero.mp this
    · intro h; simp [h]
