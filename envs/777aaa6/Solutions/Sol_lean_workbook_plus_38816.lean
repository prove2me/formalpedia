-- Prove2me | solution 1 for lean_workbook_plus_38816
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:53:49.631294+00:00
-- url     : https://prove2.me/submissions/b127443c-5fdc-42d3-8cc9-a6556d5df3ca

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :
  ∀ A B C : ℝ, A + B + C = 180 → (90 - A / 2) + (90 - B / 2) + (90 - C / 2) = 180 := by
  (intros; linarith)
