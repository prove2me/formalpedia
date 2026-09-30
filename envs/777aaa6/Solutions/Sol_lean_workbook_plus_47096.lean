-- Prove2me | solution 1 for lean_workbook_plus_47096
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:12:33.149969+00:00
-- url     : https://prove2.me/submissions/049b83fc-b763-4307-bd99-f744f28d5249

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∃ f : ℤ → ℤ, ∀ x, f x = - x^2 := by
  aesop
