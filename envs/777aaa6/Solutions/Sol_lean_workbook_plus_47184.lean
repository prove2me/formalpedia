-- Prove2me | solution 1 for lean_workbook_plus_47184
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:02:42.57064+00:00
-- url     : https://prove2.me/submissions/75989ed2-f658-45ee-adb1-3839d4f9f813

import Mathlib.Analysis.Complex.Basic

theorem solution {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^2 / b + b^2 / c + c^2 / a ≥ a + b + c := by
  obtain ⟨ha, hb, hc⟩ := hx
  have h1 : 2 * a - b ≤ a^2 / b := by
    rw [le_div_iff₀ hb]; nlinarith [sq_nonneg (a - b)]
  have h2 : 2 * b - c ≤ b^2 / c := by
    rw [le_div_iff₀ hc]; nlinarith [sq_nonneg (b - c)]
  have h3 : 2 * c - a ≤ c^2 / a := by
    rw [le_div_iff₀ ha]; nlinarith [sq_nonneg (c - a)]
  linarith
