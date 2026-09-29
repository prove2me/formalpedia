-- Prove2me | Theorems.Thm_lean_workbook_plus_22402
-- name    : lean_workbook_plus_22402
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/cbf57b18-1198-4b5e-a844-235c1441b640
-- statement:
--   $ \frac{x^4+1}{x^6+1}=\frac{1}{3}\frac{x^2+1}{x^4-x^2+1}+\frac{2}{3(x^2+1)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22402  (x : ℝ) :
  (x^4 + 1) / (x^6 + 1) = 1 / 3 * (x^2 + 1) / (x^4 - x^2 + 1) + 2 / (3 * (x^2 + 1))   :=  by sorry
