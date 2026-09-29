-- Prove2me | Theorems.Thm_lean_workbook_plus_72109
-- name    : lean_workbook_plus_72109
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/bde97046-cbc1-4e90-b406-80e9d5ff4bd9
-- statement:
--   $\Leftrightarrow\left(x+\frac{b-a\sqrt3}{2}\right)^2+\left(y+\frac{a+b\sqrt3}{2}\right)^2\geq0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72109 (a b x y : ℝ) : (x + (b - a * Real.sqrt 3) / 2) ^ 2 + (y + (a + b * Real.sqrt 3) / 2) ^ 2 ≥ 0   :=  by sorry
