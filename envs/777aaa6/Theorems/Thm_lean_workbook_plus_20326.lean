-- Prove2me | Theorems.Thm_lean_workbook_plus_20326
-- name    : lean_workbook_plus_20326
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/69c840ee-a666-418d-a6fb-70b0ff787125
-- statement:
--   Prove that $0\le x(1-x)\le\frac14$ for all $x\in [0,1]$ using the Arithmetic Mean-Geometric Mean (AM-GM) inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20326 (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
  0 ≤ x * (1 - x) ∧ x * (1 - x) ≤ 1 / 4   :=  by sorry
