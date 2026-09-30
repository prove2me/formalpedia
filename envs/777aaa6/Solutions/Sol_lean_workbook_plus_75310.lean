-- Prove2me | solution 1 for lean_workbook_plus_75310
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:03:38.85185+00:00
-- url     : https://prove2.me/submissions/10893b52-0110-4db4-ada0-23901459224a

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∃ f : ℝ → ℝ, ∀ x, f x = |x| := by
  aesop
