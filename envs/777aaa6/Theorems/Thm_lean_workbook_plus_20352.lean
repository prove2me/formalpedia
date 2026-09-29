-- Prove2me | Theorems.Thm_lean_workbook_plus_20352
-- name    : lean_workbook_plus_20352
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/4a608e93-0023-40ad-a411-0490cfbc49d3
-- statement:
--   Prove that $\sum_{cyc} (x^3+y^3-x^2y-xy^2) = \sum_{cyc} (x-y)^2(x+y) \ge 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20352 : ∀ x y z : ℝ, 0 ≤ ∑ i in {x, y, z}, (x^3 + y^3 - x^2*y - x*y^2)   :=  by sorry
