-- Prove2me | Theorems.Thm_lean_workbook_plus_22674
-- name    : lean_workbook_plus_22674
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/6a75c12b-fa84-443f-97c6-6ebc06695545
-- statement:
--   For positive $x$, prove that $\frac{x^4 +3}{x+2} \geq \frac{8}{9} x+ \frac{4}{9}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22674 (x : ℝ) (hx : 0 < x) : (x^4 + 3) / (x + 2) ≥ 8 / 9 * x + 4 / 9   :=  by sorry
