-- Prove2me | Theorems.Thm_RybinAI2026_P01_trigKernel_weight_monotonicity
-- name    : RybinAI2026.P01.trigKernel_weight_monotonicity
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T01:21:11.133146+00:00
-- url     : https://prove2.me/theorems/88c5e122-baed-48dd-925d-b899b888b4d0
-- title:
--   Two monotonicities of the transformed pair kernel
-- statement:
--   For nonnegative w1 <= w2, the trigonometric kernel integral K(w)=integral_0^(pi/2) (1+2w sin(theta)cos(theta))^(-1) dtheta decreases with w, while (1+w)K(w) increases with w. The second comparison uses 2 sin(theta)cos(theta) <= 1 pointwise.
-- source:
--   Independent scalar consequence of the finite trigonometric representation for sqrt(t)*psi(t). It supplies the increasing-G and antitone slope-weight properties needed by the two branches of the aligned diagonal pair proof, without differentiating the parameterized psi integral.

import Mathlib

theorem RybinAI2026.P01.trigKernel_weight_monotonicity (w1 w2 : ℝ)
    (hw1 : 0 ≤ w1) (hw12 : w1 ≤ w2) :
    let K : ℝ → ℝ := fun w =>
      ∫ θ in (0 : ℝ)..(Real.pi / 2),
        1 / (1 + 2 * w * Real.sin θ * Real.cos θ)
    K w2 ≤ K w1 ∧ (1 + w1) * K w1 ≤ (1 + w2) * K w2 := by
  sorry
