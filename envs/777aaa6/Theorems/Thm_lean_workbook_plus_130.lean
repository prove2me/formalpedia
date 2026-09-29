-- Prove2me | Theorems.Thm_lean_workbook_plus_130
-- name    : lean_workbook_plus_130
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/ac377d66-272f-4499-b499-700a914dd207
-- statement:
--   $f(x) = \left\{\begin{aligned} &0 &&, \: 0 \le x \le \frac{1}{3}\\ &x-\frac{1}{3} &&, \frac{1}{3} < x \le 1 \end{aligned} \right.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_130 (x : ℝ) (f : ℝ → ℝ) (hf: f x = if x ∈ Set.Icc 0 (1/3) then 0 else x - 1/3) : f x = if x ∈ Set.Icc 0 (1/3) then 0 else x - 1/3   :=  by sorry
