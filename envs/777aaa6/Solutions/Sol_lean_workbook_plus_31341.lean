-- Prove2me | solution 1 for lean_workbook_plus_31341
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:40:34.897313+00:00
-- url     : https://prove2.me/submissions/689a1a85-cfc5-4d6d-8124-0aba113be533

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x y z : ℤ, x * y * z = x * (y * z) := by
  (intros; linarith)
