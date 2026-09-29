-- Prove2me | solution 1 for lean_workbook_plus_35096
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:39:36.36281+00:00
-- url     : https://prove2.me/submissions/78bf569c-7077-40de-a756-11ac218e9b91

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b : ℤ, a^11 * b^10 = b^10 * a^11 := by
  (intros; linarith)
