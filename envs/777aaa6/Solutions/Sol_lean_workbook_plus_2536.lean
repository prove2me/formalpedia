-- Prove2me | solution 1 for lean_workbook_plus_2536
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:24:53.880892+00:00
-- url     : https://prove2.me/submissions/8b410d89-2a2b-4ad3-ac97-7a97097bce9f

import Mathlib

theorem solution (x : ℝ) (hx : 1 ≤ x ∧ x ≤ 11) : 1 ≤ ⌊x⌋ ∧ ⌊x⌋ ≤ 11 := by
  constructor
  · exact Int.le_floor.mpr (by simpa using hx.1)
  · exact Int.floor_le_iff.mpr (by norm_num; linarith [hx.2])
