-- Prove2me | solution 1 for lean_workbook_plus_7123
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:10:36.677846+00:00
-- url     : https://prove2.me/submissions/18859313-2ac1-4a26-b652-dc1720899466

import Mathlib.Analysis.Complex.Basic

theorem solution (hx: 1 < 10) (h : 11 ≠ 0): ∃ p, p ∣ 10^11 - 1 ∧ ¬ p ∣ 9 := by
  refine ⟨21649, ?_, ?_⟩
  · norm_num
  · norm_num
