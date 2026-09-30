-- Prove2me | solution 1 for lean_workbook_plus_31615
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:53:22.05734+00:00
-- url     : https://prove2.me/submissions/59b0585f-6d91-43b4-98e5-c849ef58d8b6

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∀ n:ℕ, (10^n + 3) % 3 = 1 := by
  norm_num [Nat.pow_mod, Nat.add_mod, Nat.mul_mod]
