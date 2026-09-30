-- Prove2me | solution 1 for lean_workbook_plus_71002
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:17:26.152285+00:00
-- url     : https://prove2.me/submissions/0e8182bc-ef0f-49d7-bb14-06bac0d5cf3e

import Mathlib.Analysis.Complex.Basic

theorem solution (t : ℕ) (h : t ∣ (t + 3)^2 - 3) : t ∣ 3^3 - 3 := by
  have h6 : t ∣ 6 := by
    have h1 : (t + 3)^2 - 3 = t * (t + 6) + 6 := by
      have : (t + 3)^2 = t * (t + 6) + 9 := by ring
      omega
    rw [h1] at h
    exact (Nat.dvd_add_right (Dvd.intro _ rfl)).mp h
  exact dvd_trans h6 (by norm_num)
