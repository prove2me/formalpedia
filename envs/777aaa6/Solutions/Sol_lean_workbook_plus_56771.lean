-- Prove2me | solution 1 for lean_workbook_plus_56771
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:41:55.80771+00:00
-- url     : https://prove2.me/submissions/6a40e03f-3bdb-4b6f-b946-3a496c7839d1

import Mathlib.Analysis.Complex.Basic

theorem solution (a₁ a₂ a₃ : ℝ) (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) (h₃ : 0 ≤ a₃) (h : (1 + a₁) * (1 + a₂) * (1 + a₃) = 8) : a₁ * a₂ * a₃ ≤ 1 := by
  -- three-variable AM-GM in polynomial form
  have amgm : ∀ b₁ b₂ b₃ : ℝ, 0 ≤ b₁ → 0 ≤ b₂ → 0 ≤ b₃ →
      27 * (b₁ * b₂ * b₃) ≤ (b₁ + b₂ + b₃) ^ 3 := by
    intro b₁ b₂ b₃ hb₁ hb₂ hb₃
    nlinarith [mul_nonneg (add_nonneg (add_nonneg hb₁ hb₂) hb₃) (sq_nonneg (b₁ - b₂)),
      mul_nonneg (add_nonneg (add_nonneg hb₁ hb₂) hb₃) (sq_nonneg (b₂ - b₃)),
      mul_nonneg (add_nonneg (add_nonneg hb₁ hb₂) hb₃) (sq_nonneg (b₁ - b₃)),
      mul_nonneg hb₁ (sq_nonneg (b₂ - b₃)), mul_nonneg hb₂ (sq_nonneg (b₁ - b₃)),
      mul_nonneg hb₃ (sq_nonneg (b₁ - b₂))]
  by_contra hp
  push_neg at hp
  have h' : 1 + (a₁ + a₂ + a₃) + (a₁ * a₂ + a₂ * a₃ + a₁ * a₃) + a₁ * a₂ * a₃ = 8 := by
    linear_combination h
  have hs1 := amgm a₁ a₂ a₃ h₁ h₂ h₃
  have hs2 := amgm (a₁ * a₂) (a₂ * a₃) (a₁ * a₃) (mul_nonneg h₁ h₂) (mul_nonneg h₂ h₃) (mul_nonneg h₁ h₃)
  have hprod : a₁ * a₂ * (a₂ * a₃) * (a₁ * a₃) = (a₁ * a₂ * a₃) ^ 2 := by ring
  rw [hprod] at hs2
  have hp2 : 1 < (a₁ * a₂ * a₃) ^ 2 := by nlinarith
  have hgt1 : 3 < a₁ + a₂ + a₃ := by
    by_contra hle
    push_neg at hle
    have : (a₁ + a₂ + a₃) ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ (by positivity) hle 3
    nlinarith
  have hgt2 : 3 < a₁ * a₂ + a₂ * a₃ + a₁ * a₃ := by
    by_contra hle
    push_neg at hle
    have : (a₁ * a₂ + a₂ * a₃ + a₁ * a₃) ^ 3 ≤ 3 ^ 3 :=
      pow_le_pow_left₀ (by positivity) hle 3
    nlinarith
  linarith
