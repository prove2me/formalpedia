-- Prove2me | Theorems.Thm_lean_workbook_plus_73244
-- name    : lean_workbook_plus_73244
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/b3a8b1a3-e69a-49c8-91d1-4ee04da76388
-- statement:
--   Given $ f(x)=\cos\left(\frac{\pi}{x}\right)$ is continuous on $ (0,\infty).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73244 : ContinuousOn (fun x : ℝ => Real.cos (Real.pi / x)) (Set.Ioi 0)   :=  by sorry
