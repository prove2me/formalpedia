-- Prove2me | Theorems.Thm_lean_workbook_plus_31909
-- name    : lean_workbook_plus_31909
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/6831ffc5-2c41-4581-99cb-25099579dff4
-- statement:
--   (x - 1)(x - 3) $\le$ 0 $\Rightarrow$ x $\in$ [1,3]
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31909 (x : ℝ) (hx: (x - 1) * (x - 3) ≤ 0) : 1 ≤ x ∧ x ≤ 3   :=  by sorry
