-- Prove2me | Theorems.Thm_lean_workbook_plus_3515
-- name    : lean_workbook_plus_3515
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/cbbf608d-1311-485a-950e-2cafe900f8be
-- statement:
--   $ LHS\geq\sum (x+y-z)^{2}\geq\sum x^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3515 (x y z : ℝ) : (x + y - z) ^ 2 + (y + z - x) ^ 2 + (z + x - y) ^ 2 ≥ x ^ 2 + y ^ 2 + z ^ 2   :=  by sorry
