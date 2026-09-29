-- Prove2me | Theorems.Thm_lean_workbook_plus_70810
-- name    : lean_workbook_plus_70810
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/b98fa1eb-b984-41de-999b-afb957c1c840
-- statement:
--   $$F(x) = \begin{cases}0, & x = 0\\1, & \text{otherwise}\end{cases}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70810 (F : ℝ → ℝ) (x : ℝ) (hf: F x = if x = 0 then 0 else 1) : F x = if x = 0 then 0 else 1   :=  by sorry
