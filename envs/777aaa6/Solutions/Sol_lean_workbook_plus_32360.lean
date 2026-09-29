-- Prove2me | solution 1 for lean_workbook_plus_32360
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:43:56.9123+00:00
-- url     : https://prove2.me/submissions/c185e147-4a79-4a54-b353-9f9c829cc331

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z p q r : ℝ) (h₁ : x + y + z = p + 2*q) (h₂ : y = q + r) : x + z = p + q - r := by
  (intros; linarith)
