-- Prove2me | solution 1 for lean_workbook_plus_72262
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:20:36.857652+00:00
-- url     : https://prove2.me/submissions/36770de9-060b-4ee3-b222-950e580f8280

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x + y = 2) : x * y ≤ 1 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
