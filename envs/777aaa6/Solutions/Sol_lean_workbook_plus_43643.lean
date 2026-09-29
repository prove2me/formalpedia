-- Prove2me | solution 1 for lean_workbook_plus_43643
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:29:08.023426+00:00
-- url     : https://prove2.me/submissions/df22df9d-297a-4d92-8e64-552bd09f53e4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :  ∀ a b c d : ℝ, (1 - a) * (1 - b) * (1 - c) * (1 - d) > 0 → 1 + a * b + a * c + a * d + b * c + b * d + c * d - (a * b * c + a * b * d + a * c * d + b * c * d) + a * b * c * d > a + b + c + d := by
  (intros; linarith)
