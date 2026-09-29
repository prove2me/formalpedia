-- Prove2me | Theorems.Thm_lean_workbook_plus_69149
-- name    : lean_workbook_plus_69149
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/e22fbadc-cb34-43aa-a773-e6d00ed53442
-- statement:
--   ProofLet $y \in[ 0, 4k-\frac{1}{2}]$ , then $\frac{1}{8} + \frac{y}{4} \in [0,k]$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69149 (y : ℝ) (k : ℝ) (hy: y ∈ Set.Icc 0 (4 * k - 1 / 2)) : 1 / 8 + y / 4 ∈ Set.Icc 0 k   :=  by sorry
