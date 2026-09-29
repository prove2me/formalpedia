-- Prove2me | solution 1 for lean_workbook_plus_32901
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:38:48.808723+00:00
-- url     : https://prove2.me/submissions/9a620ede-7300-4e4f-af4f-cbbd592abcc4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ k : ℤ, (k - 1) * k * (k + 1) * (k + 2) = (k ^ 3 - k) * (k + 2) := by
  (intros; linarith)
