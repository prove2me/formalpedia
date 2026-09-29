-- Prove2me | solution 1 for lean_workbook_plus_59378
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:43:43.785714+00:00
-- url     : https://prove2.me/submissions/21860934-9ad6-4974-a146-24c5217806e7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  (11 + 2 * Real.sqrt 10) / 81 * (3 * a ^ 2 + (4 - Real.sqrt 10) * b ^ 2 + 3 * c ^ 2 + (2 * Real.sqrt 10 - 5) * b * (c + a) - 3 * Real.sqrt 10 * c * a) ^ 2 +
    (11 + 2 * Real.sqrt 10) / 81 * (3 * b ^ 2 + (4 - Real.sqrt 10) * c ^ 2 + 3 * a ^ 2 + (2 * Real.sqrt 10 - 5) * c * (a + b) - 3 * Real.sqrt 10 * a * b) ^ 2 +
    (11 + 2 * Real.sqrt 10) / 81 * (3 * c ^ 2 + (4 - Real.sqrt 10) * a ^ 2 + 3 * b ^ 2 + (2 * Real.sqrt 10 - 5) * a * (b + c) - 3 * Real.sqrt 10 * b * c) ^ 2 ≥ 0 := by
  (intros; positivity)
