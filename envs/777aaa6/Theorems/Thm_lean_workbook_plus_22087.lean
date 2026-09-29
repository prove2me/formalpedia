-- Prove2me | Theorems.Thm_lean_workbook_plus_22087
-- name    : lean_workbook_plus_22087
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/c3f5ee95-3cd1-49a1-b497-2b83f8ecb600
-- statement:
--   Prove $x+\frac{1}{x+1} \geq \frac{3}{4}(x+1)$ for all positive real numbers $x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22087 (x : ℝ) (hx : 0 < x) : x + 1 / (x + 1) ≥ 3 / 4 * (x + 1)   :=  by sorry
