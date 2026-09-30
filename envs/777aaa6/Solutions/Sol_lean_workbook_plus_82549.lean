-- Prove2me | solution 1 for lean_workbook_plus_82549
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:07:05.768605+00:00
-- url     : https://prove2.me/submissions/7789aacb-f24d-4721-857b-0136a9db9d56

import Mathlib

theorem solution (α β γ : ℝ) (h₁ : α * β + β * γ + γ * α = 0)
    (h₂ : α * β * γ = 1) : 1 / γ = 1 / -α + 1 / -β := by
  have ha : α ≠ 0 := by intro h; simp [h] at h₂
  have hb : β ≠ 0 := by intro h; simp [h] at h₂
  have hc : γ ≠ 0 := by intro h; simp [h] at h₂
  field_simp
  nlinarith
