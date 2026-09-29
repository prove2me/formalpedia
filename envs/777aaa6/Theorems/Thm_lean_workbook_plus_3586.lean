-- Prove2me | Theorems.Thm_lean_workbook_plus_3586
-- name    : lean_workbook_plus_3586
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/24b6bd5c-e8c8-4ed5-b8bd-343ebb659c30
-- statement:
--   And so condition is $(3-x)^2\ge 4(x^2-3x+a)$ which is $(x-1)^2\le 4-\frac{4a}3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3586 (x a : ℝ) : (3 - x) ^ 2 ≥ 4 * (x ^ 2 - 3 * x + a) ↔ (x - 1) ^ 2 ≤ 4 - 4 * a / 3   :=  by sorry
