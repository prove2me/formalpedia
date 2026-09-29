-- Prove2me | solution 1 for lean_workbook_plus_55458
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:01:37.026278+00:00
-- url     : https://prove2.me/submissions/74a141b8-7ff8-4924-b214-d1296dd4f761

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (c : ℝ)
  (h₀ : 0 ≤ c) :
  c^3 ≤ c^3 + c ∧ c^3 + c < (c + 1)^3 := by
  (intros; constructor <;> nlinarith [sq_nonneg (c)])
