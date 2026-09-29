-- Prove2me | solution 1 for lean_workbook_plus_36540
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:04:32.902826+00:00
-- url     : https://prove2.me/submissions/2a777544-f2d9-40f2-97aa-fdcfab4f528d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  a ^ 3 * b ^ 3 + b ^ 3 * c ^ 3 + c ^ 3 * a ^ 3 - a * b * c * (a ^ 3 + b ^ 3 + c ^ 3) =
    (a * b - c ^ 2) * (a * c - b ^ 2) * (b * c - a ^ 2) := by
  (intros; linarith)
