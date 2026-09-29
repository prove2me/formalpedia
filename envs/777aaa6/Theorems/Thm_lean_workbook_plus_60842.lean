-- Prove2me | Theorems.Thm_lean_workbook_plus_60842
-- name    : lean_workbook_plus_60842
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/e0f9d027-0517-431f-99cb-2c0d4793b62b
-- statement:
--   Then $f(x)=1-f(0)-x$ , and $f(0)=1-f(0)$ hence $f(0)=1/2$ . and $f(x)=\frac 12-x$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60842 (f : ℝ → ℝ) (hf: f = fun (x:ℝ) => 1 - f 0 - x) : f 0 = 1 / 2 ∧ f = fun (x:ℝ) => 1 / 2 - x   :=  by sorry
