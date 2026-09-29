-- Prove2me | solution 1 for lean_workbook_plus_15661
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:49:08.844563+00:00
-- url     : https://prove2.me/submissions/f1c4d8b2-5c4d-49b1-bc8e-c9e647cd6345

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (M : ℤ) (h₁ : 287 ≤ M) (h₂ : M ≤ 442) : ¬ M = 0 := by
  (intros; positivity)
