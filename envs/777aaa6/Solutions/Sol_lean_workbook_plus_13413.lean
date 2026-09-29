-- Prove2me | solution 1 for lean_workbook_plus_13413
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:19:29.270388+00:00
-- url     : https://prove2.me/submissions/ccd51ca0-8789-414e-afe3-50800eefc332

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℂ, (a^2 + 1) * (b^2 + 1) * (c^2 + 1) = a^2 * b^2 * c^2 + a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + a^2 + b^2 + c^2 + 1 := by
  (intros; ring)
