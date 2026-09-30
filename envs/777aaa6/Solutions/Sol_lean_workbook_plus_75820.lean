-- Prove2me | solution 1 for lean_workbook_plus_75820
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:44:06.764073+00:00
-- url     : https://prove2.me/submissions/b96c9964-45a0-4e7d-9a10-8e2a76370c2e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c d : ℝ) (hab : 0 < a ∧ a < 1) (hbc : 0 < b ∧ b < 1)
    (hcd : 0 < c ∧ c < 1) (hded : 0 < d ∧ d < 1) :
    (1 - a) * (1 - b) * (1 - c) * (1 - d) > 1 - a - b - c - d := by
  obtain ⟨ha, ha'⟩ := hab
  obtain ⟨hb, hb'⟩ := hbc
  obtain ⟨hc, hc'⟩ := hcd
  obtain ⟨hd, hd'⟩ := hded
  have hc₁ : 0 < 1 - c := sub_pos.mpr hc'
  have hd₁ : 0 < 1 - d := sub_pos.mpr hd'
  have hcert : 0 < a * b * (1 - c) * (1 - d) +
      c * (a + b) * (1 - d) + d * (a + b + c) := by positivity
  nlinarith only [hcert]

#print axioms solution
