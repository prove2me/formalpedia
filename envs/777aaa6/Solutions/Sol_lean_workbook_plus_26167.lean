-- Prove2me | solution 1 for lean_workbook_plus_26167
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:20.919862+00:00
-- url     : https://prove2.me/submissions/7d4ae5f6-b662-4b0d-983d-72e16bbc6d1d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c d p q r : ℝ} (h1 : p = b * c + a * d) (h2 : q = a * b + c * d) (h3 : r = a * c + b * d) : (p - q) ^ 2 + (q - r) ^ 2 + (r - p) ^ 2 ≥ 0 := by
  (intros; positivity)
