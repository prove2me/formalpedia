-- Prove2me | solution 1 for BookSixth.round_frame_angles
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T09:37:29.727467+00:00
-- url     : https://prove2.me/submissions/62d8d5df-2583-4024-93ff-46935c7d6209

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_pointwise_isotopy_wrappers

noncomputable section

open scoped BigOperators
open BookSixth

set_option maxHeartbeats 4000000

/-- Three coordinate-plane angles align the orthonormal frame of a round circle
`(u, v)` with the coordinate axes: `u` is carried to the first unit vector and the
leading coordinate of `v` is killed. -/
theorem solution :
    ∀ (u v : Fin 3 → ℝ),
      (∑ i, u i * u i) = 1 → (∑ i, v i * v i) = 1 → (∑ i, u i * v i) = 0 →
      ∃ θ1 θ2 θ3 : ℝ,
        Real.sin θ1 * u 0 + Real.cos θ1 * u 1 = 0 ∧
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
        Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) - Real.sin θ2 * v 2 = 0 := by
  intro u v hu hv huv
  simp only [Fin.sum_univ_three] at hu hv huv
  -- The third conjunct of `pointwise_isotopy_wrappers` is the two-input angle
  -- lemma: for any `a b` there is a `θ` killing the first coordinate and
  -- keeping the second nonnegative. It is used three times in sequence, once
  -- per coordinate plane. There is no separate `angle_pw` name.
  obtain ⟨-, -, hangle⟩ := BookSixth.pointwise_isotopy_wrappers
  obtain ⟨θ1, h1a, h1b⟩ := hangle (u 0) (u 1)
  obtain ⟨θ2, h2a, h2b⟩ := hangle
    (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) (u 2)
  obtain ⟨θ3, h3a, h3b⟩ := hangle (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
      (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + Real.cos θ2 * v 2)
  have p1 : (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) ^ 2
      + (Real.sin θ1 * u 0 + Real.cos θ1 * u 1) ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
    linear_combination (u 0 ^ 2 + u 1 ^ 2) * Real.cos_sq_add_sin_sq θ1
  have p2 : (Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2) ^ 2
      + (Real.sin θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) + Real.cos θ2 * u 2) ^ 2
      = (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) ^ 2 + u 2 ^ 2 := by
    linear_combination ((Real.cos θ1 * u 0 - Real.sin θ1 * u 1) ^ 2 + u 2 ^ 2)
      * Real.cos_sq_add_sin_sq θ2
  have hρ2sq : (Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2) ^ 2
      = 1 := by
    linear_combination p2 + p1 + hu
      - (Real.sin θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) + Real.cos θ2 * u 2) * h2a
      - (Real.sin θ1 * u 0 + Real.cos θ1 * u 1) * h1a
  have hρ2 : Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2 = 1 := by
    have hm : ((Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2) - 1)
        * ((Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2) + 1)
        = 0 := by linear_combination hρ2sq
    rcases mul_eq_zero.1 hm with h | h
    · linarith
    · linarith
  have q1 : (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
      + (Real.sin θ1 * u 0 + Real.cos θ1 * u 1) * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
      = u 0 * v 0 + u 1 * v 1 := by
    linear_combination (u 0 * v 0 + u 1 * v 1) * Real.cos_sq_add_sin_sq θ1
  have q2 : (Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2)
        * (Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) - Real.sin θ2 * v 2)
      + (Real.sin θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) + Real.cos θ2 * u 2)
        * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + Real.cos θ2 * v 2)
      = (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
        + u 2 * v 2 := by
    linear_combination ((Real.cos θ1 * u 0 - Real.sin θ1 * u 1)
      * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + u 2 * v 2) * Real.cos_sq_add_sin_sq θ2
  have hd0 : Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) - Real.sin θ2 * v 2 = 0 := by
    linear_combination q2 + q1 + huv
      - (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + Real.cos θ2 * v 2) * h2a
      - (Real.sin θ1 * v 0 + Real.cos θ1 * v 1) * h1a
      - (Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) - Real.sin θ2 * v 2) * hρ2
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
  have hρ3 : Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2) = 1 := by
    have hm : ((Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2)) - 1) * ((Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2)) + 1) = 0 := by linear_combination hρ3sq
    rcases mul_eq_zero.1 hm with h | h
    · linarith
    · linarith
  refine ⟨θ1, θ2, θ3, h1a, h1b, h2a, h2b, h3a, h3b, hρ2, hd0⟩
