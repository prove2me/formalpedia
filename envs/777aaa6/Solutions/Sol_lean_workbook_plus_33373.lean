-- Prove2me | solution 1 for lean_workbook_plus_33373
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:12:43.263611+00:00
-- url     : https://prove2.me/submissions/63c4e5b4-31d3-40a1-bca3-8802089411fa

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∃ f : ℤ → ℤ, ∀ x, f x = x + 1 := by
  aesop
