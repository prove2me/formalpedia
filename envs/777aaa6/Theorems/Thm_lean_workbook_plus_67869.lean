-- Prove2me | Theorems.Thm_lean_workbook_plus_67869
-- name    : lean_workbook_plus_67869
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/a309ee88-2b07-4815-8da7-6d852e0ba86c
-- statement:
--   ProofLet $y \in[ 0, 4k-\frac{1}{2}]$ , then $\frac{1}{8} + \frac{y}{4} \in [0,k]$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67869 (y : ℝ) (k : ℝ) (hy : 0 ≤ y ∧ y ≤ 4 * k - 1 / 2) :
  1 / 8 + y / 4 ∈ Set.Icc 0 k   :=  by sorry
