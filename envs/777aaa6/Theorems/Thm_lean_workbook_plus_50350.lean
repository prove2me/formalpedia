-- Prove2me | Theorems.Thm_lean_workbook_plus_50350
-- name    : lean_workbook_plus_50350
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/5fcc9b70-0f5b-4f1c-8f80-f9f495bda15d
-- statement:
--   Show that for $x > 1$, $f(x) = \ln \frac{x(x^2 + 3)}{3x^2 + 1} < x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50350 (x : ℝ) (hx : 1 < x) : Real.log (x * (x ^ 2 + 3) / (3 * x ^ 2 + 1)) < x   :=  by sorry
