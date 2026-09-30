-- Prove2me | solution 1 for lean_workbook_plus_42269
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:14:27.468647+00:00
-- url     : https://prove2.me/submissions/84b7d408-0973-4ee3-a87a-6c76d3f5142c

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ)
  (h₀ : x = 100)
  (h₁ : (1 - 0.3) * (1 - 0.2) = 0.56) :
  x * (1 - 0.3) * (1 - 0.2) = 56 := by
  subst h₀
  norm_num
