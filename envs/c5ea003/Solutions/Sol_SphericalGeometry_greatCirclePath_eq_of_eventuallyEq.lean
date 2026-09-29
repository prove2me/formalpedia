-- Prove2me | solution 1 for SphericalGeometry.greatCirclePath_eq_of_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-28T00:55:47.650598+00:00
-- url     : https://prove2.me/submissions/be91ba72-86a7-4e5d-a598-738522a3ccb0

import Definitions.Def_spherical_great_circle
import Theorems.Thm_TrigPolynomial_coeffs_eq_zero_of_eventually_eq_zero

open SphericalGeometry Filter Topology

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v1 v2 u1 u2 : E) (t0 : ℝ)
    (h : ∀ᶠ t in 𝓝 t0, greatCirclePath v1 v2 t = greatCirclePath u1 u2 t) :
    v1 = u1 ∧ v2 = u2 := by
  have key : ∀ x : E, (inner ℝ (v1 - u1) x : ℝ) = 0 ∧ (inner ℝ (v2 - u2) x : ℝ) = 0 := by
    intro x
    have hev : ∀ᶠ t in 𝓝 t0,
        (0:ℝ) + (inner ℝ (v1 - u1) x : ℝ) * Real.cos (1 * t)
          + (inner ℝ (v2 - u2) x : ℝ) * Real.sin (1 * t) = 0 := by
      filter_upwards [h] with t ht
      have hd : (inner ℝ (greatCirclePath v1 v2 t - greatCirclePath u1 u2 t) x : ℝ) = 0 := by
        rw [ht, sub_self, inner_zero_left]
      simp only [greatCirclePath, inner_sub_left, inner_add_left, real_inner_smul_left,
        one_mul] at hd ⊢
      linarith
    obtain ⟨_, hA, hB⟩ :=
      TrigPolynomial.coeffs_eq_zero_of_eventually_eq_zero 1 one_ne_zero 0
        (inner ℝ (v1 - u1) x) (inner ℝ (v2 - u2) x) t0 hev
    exact ⟨hA, hB⟩
  constructor
  · have := (key (v1 - u1)).1
    have h2 : v1 - u1 = 0 := by
      rwa [inner_self_eq_zero] at this
    exact sub_eq_zero.mp h2
  · have := (key (v2 - u2)).2
    have h2 : v2 - u2 = 0 := by
      rwa [inner_self_eq_zero] at this
    exact sub_eq_zero.mp h2
