-- Prove2me | solution 1 for lean_workbook_plus_9088
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:39:46.139473+00:00
-- url     : https://prove2.me/submissions/c394f848-a8b4-4da6-99b9-fef77f453ee0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p : ℝ → ℝ) (hp : ∀ x, p x = x) : ∀ x, p x = x := by
  (intros; simp_all)
