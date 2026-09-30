-- Prove2me | solution 1 for lean_workbook_plus_65561
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:18:49.204824+00:00
-- url     : https://prove2.me/submissions/7103c618-dff8-4498-a3ff-ca97982fd3b9

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ ∃ (a : ℤ), (a : ℝ)^2 = 15 := by
  rintro ⟨a, ha⟩
  have h : a ^ 2 = 15 := by exact_mod_cast ha
  have h1 : a ≤ 3 ∨ 4 ≤ a := by omega
  have h2 : -3 ≤ a ∨ a ≤ -4 := by omega
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> nlinarith
