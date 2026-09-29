-- Prove2me | solution 1 for lean_workbook_plus_73528
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:50:57.027219+00:00
-- url     : https://prove2.me/submissions/3b88de44-ee72-4aaa-bd43-0246b259247b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∃ (u : ℕ → ℝ), ∀ n, Even n → u n = n ∧ Odd n → u n = 1 / n := by
  (intros; simp_all)
