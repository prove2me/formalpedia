-- Prove2me | solution 1 for RybinAI2026.P01.pair_dot_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T22:05:21.595422+00:00
-- url     : https://prove2.me/submissions/db2c7f56-8c33-4da8-ba02-fc587d2b49c9

import Mathlib

theorem solution {r₁ r₂ s₁ s₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂)
    (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂)
    (hr : r₁ ^ 2 + r₂ ^ 2 ≤ 1)
    (hs : s₁ ^ 2 + s₂ ^ 2 ≤ 1) :
    r₁ * s₁ + r₂ * s₂ ≤ 1 := by
  have hcs :
      (r₁ * s₁ + r₂ * s₂) ^ 2 ≤
        (r₁ ^ 2 + r₂ ^ 2) * (s₁ ^ 2 + s₂ ^ 2) := by
    nlinarith [sq_nonneg (r₁ * s₂ - r₂ * s₁)]
  have hr0 : 0 ≤ r₁ ^ 2 + r₂ ^ 2 := by positivity
  have hprod :
      (r₁ ^ 2 + r₂ ^ 2) * (s₁ ^ 2 + s₂ ^ 2) ≤ 1 := by
    calc
      (r₁ ^ 2 + r₂ ^ 2) * (s₁ ^ 2 + s₂ ^ 2) ≤
          (r₁ ^ 2 + r₂ ^ 2) * 1 := mul_le_mul_of_nonneg_left hs hr0
      _ = r₁ ^ 2 + r₂ ^ 2 := by ring
      _ ≤ 1 := hr
  have hsq : (r₁ * s₁ + r₂ * s₂) ^ 2 ≤ 1 := le_trans hcs hprod
  have hnonneg : 0 ≤ r₁ * s₁ + r₂ * s₂ :=
    add_nonneg (mul_nonneg hr₁ hs₁) (mul_nonneg hr₂ hs₂)
  nlinarith
