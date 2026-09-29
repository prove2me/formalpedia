-- Prove2me | Theorems.Thm_lean_workbook_plus_64162
-- name    : lean_workbook_plus_64162
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/c52a726f-e124-4932-94d5-a520302d1325
-- statement:
--   Prove that the function $f(x) = \frac{1}{x}$ is bijective
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64162 : Function.Bijective (fun x : ℝ => 1 / x)   :=  by sorry
