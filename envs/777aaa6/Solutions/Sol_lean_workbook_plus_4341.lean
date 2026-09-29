-- Prove2me | solution 1 for lean_workbook_plus_4341
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:51:32.913926+00:00
-- url     : https://prove2.me/submissions/258e9e20-726f-466b-8112-ac96b30a6593

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ n : ℤ, n^6 - 1 = (n^3 - 1) * (n^3 + 1) := by
  (intros; linarith)
