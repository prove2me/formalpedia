-- Prove2me | solution 1 for lean_workbook_plus_30077
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:43:13.154746+00:00
-- url     : https://prove2.me/submissions/093bf2e6-b1ed-4889-85ee-69de3fd52c30

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : 2 * x + 114 = 1542) :
  x = 714 ∧ 2 * x + 114 = 1542 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x)])
