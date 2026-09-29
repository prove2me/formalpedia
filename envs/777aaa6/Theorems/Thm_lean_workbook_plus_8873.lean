-- Prove2me | Theorems.Thm_lean_workbook_plus_8873
-- name    : lean_workbook_plus_8873
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/e932f802-8e7d-417f-abcc-0514ca07aa5a
-- statement:
--   Prove that for any positive real number $\epsilon$, there exists an integer $n$ such that $\frac{1}{n}< \epsilon$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8873 (ε : ℝ) (hε : 0 < ε) : ∃ n : ℤ, (1 : ℝ) / n < ε   :=  by sorry
