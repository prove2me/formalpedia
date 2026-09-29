-- Prove2me | Theorems.Thm_lean_workbook_plus_22478
-- name    : lean_workbook_plus_22478
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/8e53c971-447b-4955-a4ca-742e7bf3d2f1
-- statement:
--   Show that the polynomial $f(x) = x^6 - x^5 + x^4 - x^3 + x^2 - x + \frac{3}{4}$ has no real roots.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22478 : ¬ ∃ x : ℝ, x^6 - x^5 + x^4 - x^3 + x^2 - x + 3 / 4 = 0   :=  by sorry
