-- Prove2me | solution 1 for lean_workbook_plus_58227
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:20:55.678815+00:00
-- url     : https://prove2.me/submissions/fed05635-81e5-44f5-890e-49a6866a9a7f

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ n : ℤ, Even n → n^2 % 4 = 0 := by
  rintro n ⟨k, rfl⟩
  have h : (k + k)^2 = 4 * (k * k) := by ring
  rw [h]
  omega
