-- Prove2me | solution 1 for lean_workbook_plus_81248
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:53:07.279628+00:00
-- url     : https://prove2.me/submissions/13e1030a-1c64-4365-8d6b-cf7de20e5795

import Mathlib

theorem solution (n : ℕ) :
    7 * n + 1 ∣ 8 * n + 55 → 7 * n + 1 ∣ 56 * n + 385 := by
  rintro ⟨k, hk⟩
  refine ⟨7 * k, ?_⟩
  calc
    56 * n + 385 = 7 * (8 * n + 55) := by ring
    _ = 7 * ((7 * n + 1) * k) := by rw [hk]
    _ = (7 * n + 1) * (7 * k) := by ring
