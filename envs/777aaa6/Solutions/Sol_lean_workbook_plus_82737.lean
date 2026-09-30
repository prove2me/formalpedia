-- Prove2me | solution 1 for lean_workbook_plus_82737
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:47:23.229138+00:00
-- url     : https://prove2.me/submissions/e5c7b8e5-c066-4161-b5ac-b63b3f24f5f2

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (x : ℕ) : x ∉ (∅ : Set ℕ) := by
  norm_num
