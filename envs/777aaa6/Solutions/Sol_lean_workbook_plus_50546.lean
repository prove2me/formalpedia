-- Prove2me | solution 1 for lean_workbook_plus_50546
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:53:16.465402+00:00
-- url     : https://prove2.me/submissions/19e4754e-6964-4724-b5b8-8728010f7095

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∃ f : ℕ → ℕ, ∀ m, f m = m := by
  aesop
