-- Prove2me | solution 1 for BookSixth.round_frame_v_unit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T09:39:30.458362+00:00
-- url     : https://prove2.me/submissions/e79087d6-225d-460a-9d3a-127d332c8e59

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_pointwise_isotopy_wrappers

noncomputable section

open scoped BigOperators
open BookSixth

set_option maxHeartbeats 4000000

/-- The surviving coordinate of the rotated `v` is exactly `1`, given the chain of
vanishing, sign and residual conditions and the unit-norm hypothesis on `v`. This is
the step the angle lemma cannot supply: the lemma fixes the sign of the residual but
not its magnitude, and the magnitude is the unit norm of `v` preserved along the
chain of rotations. -/
theorem solution :
    ∀ (u v : Fin 3 → ℝ) (θ1 θ2 θ3 : ℝ),
      (∑ i, v i * v i) = 1 →
      (Real.sin θ1 * u 0 + Real.cos θ1 * u 1 = 0 ∧
        0 ≤ Real.cos θ1 * u 0 - Real.sin θ1 * u 1 ∧
        Real.sin θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) + Real.cos θ2 * u 2 = 0 ∧
        0 ≤ Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2 ∧
        Real.sin θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1) +
            Real.cos θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
              + Real.cos θ2 * v 2) = 0 ∧
        0 ≤ Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1) -
            Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
              + Real.cos θ2 * v 2) ∧
        Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2 = 1 ∧
        Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) - Real.sin θ2 * v 2 = 0) →
      Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2) = 1 := by
  intro u v θ1 θ2 θ3 hv hchain
  obtain ⟨h1a, h1b, h2a, h2b, h3a, h3b, hρ2, hd0⟩ := hchain
  simp only [Fin.sum_univ_three] at hv
  have p1v : (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) ^ 2
      + (Real.sin θ1 * v 0 + Real.cos θ1 * v 1) ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    linear_combination (v 0 ^ 2 + v 1 ^ 2) * Real.cos_sq_add_sin_sq θ1
  have p2v : (Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) - Real.sin θ2 * v 2) ^ 2
      + (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + Real.cos θ2 * v 2) ^ 2
      = (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) ^ 2 + v 2 ^ 2 := by
    linear_combination ((Real.cos θ1 * v 0 - Real.sin θ1 * v 1) ^ 2 + v 2 ^ 2)
      * Real.cos_sq_add_sin_sq θ2
  have p3 : (Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2)) ^ 2
      + (Real.sin θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        + Real.cos θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2)) ^ 2
      = (Real.sin θ1 * v 0 + Real.cos θ1 * v 1) ^ 2
        + (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + Real.cos θ2 * v 2) ^ 2 := by
    linear_combination ((Real.sin θ1 * v 0 + Real.cos θ1 * v 1) ^ 2
        + (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + Real.cos θ2 * v 2) ^ 2)
      * Real.cos_sq_add_sin_sq θ3
  have hρ3sq : (Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2)) ^ 2 = 1 := by
    linear_combination p3 + p2v + p1v + hv
      - (Real.sin θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        + Real.cos θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2)) * h3a
      - (Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) - Real.sin θ2 * v 2) * hd0
  have hm : ((Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
      - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
        + Real.cos θ2 * v 2)) - 1) * ((Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
      - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
        + Real.cos θ2 * v 2)) + 1) = 0 := by linear_combination hρ3sq
  rcases mul_eq_zero.1 hm with h | h
  · linarith
  · linarith
