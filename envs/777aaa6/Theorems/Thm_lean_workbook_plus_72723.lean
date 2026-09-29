-- Prove2me | Theorems.Thm_lean_workbook_plus_72723
-- name    : lean_workbook_plus_72723
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/504416ed-ac7d-4bbc-9e20-28676eea9422
-- statement:
--   However notice that $\left(\sum_{cyc}x\right)^3=\sum_{cyc}x^3+3\sum_{cyc}x\sum_{cyc}xy-3xyz=\sum_{cyc}x^3+3\sum_{sym}x^2y+6xyz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72723 (x y z : ℝ) :
  (x + y + z) ^ 3 = x ^ 3 + y ^ 3 + z ^ 3 + 3 * (x ^ 2 * y + x ^ 2 * z + y ^ 2 * x + y ^ 2 * z + z ^ 2 * x + z ^ 2 * y) + 6 * x * y * z   :=  by sorry
