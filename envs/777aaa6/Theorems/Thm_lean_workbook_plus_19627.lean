-- Prove2me | Theorems.Thm_lean_workbook_plus_19627
-- name    : lean_workbook_plus_19627
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/d3002589-2e8d-4ed8-a5f4-a4a10a208aee
-- statement:
--   It is equivalent to $\frac{(a-b)^2}{4}+3\cdot\left(\frac{a+b}{2}-1\right)^2 \ge 0$ which is obvious
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19627 (a b : ℝ) : (a - b) ^ 2 / 4 + 3 * ((a + b) / 2 - 1) ^ 2 ≥ 0   :=  by sorry
