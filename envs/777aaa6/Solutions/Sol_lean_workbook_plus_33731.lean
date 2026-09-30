-- Prove2me | solution 1 for lean_workbook_plus_33731
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:44:17.984293+00:00
-- url     : https://prove2.me/submissions/cf572c9b-bd69-4108-8b89-542b5e8b58da

import Mathlib.Analysis.Complex.Basic

theorem solution :
  ∀ x : ℤ, -1 ≤ x ∧ x ≤ 2 → x^3 ≥ x := by
  intro x hx
  obtain ⟨h1, h2⟩ := hx
  have hc : x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;> norm_num
