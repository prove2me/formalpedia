-- Prove2me | solution 1 for lean_workbook_plus_6710
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:19:52.875662+00:00
-- url     : https://prove2.me/submissions/52586e61-8ab7-49f4-b1ce-14b0be49c75a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ u v w x : ℂ, (x - u) * (x - v) * (x - w) = x^3 - (u + v + w) * x^2 + (u * v + v * w + w * u) * x - u * v * w := by
  (intros; ring)
