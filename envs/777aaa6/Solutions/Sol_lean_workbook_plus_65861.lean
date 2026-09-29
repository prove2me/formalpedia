-- Prove2me | solution 1 for lean_workbook_plus_65861
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:53:14.849995+00:00
-- url     : https://prove2.me/submissions/acb712a7-e714-4c86-9f9c-a48cb517dc87

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b : ℝ) (h : ⌊a⌋ = b) : a - 1 ≤ b ∧ b ≤ a := by
  constructor
  · linarith [Int.sub_one_lt_floor a]
  · simpa [h] using Int.floor_le a
