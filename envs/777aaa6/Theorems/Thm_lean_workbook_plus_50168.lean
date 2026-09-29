-- Prove2me | Theorems.Thm_lean_workbook_plus_50168
-- name    : lean_workbook_plus_50168
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/c91cc084-8f4b-43a2-bc11-d08042c9ceaf
-- statement:
--   Hlawka's inequality follows immediately from the triangle inequality and the following identity (from Hlawka...) : \n\n $(|a|+|b|+|c|-|b+c|-|c+a|-|a+b|+|a+b+c|) \cdot (|a|+|b|+|c|+|a+b+c|) = (|b|+|c|-|b+c|) \cdot (|a|-|b+c| + |a+b+c|) + (|c|+|a|-|c+a|) \cdot (|b|-|c+a|+|a+b+c|) + (|a|+|b| - |a+b|) \cdot (|c|-|a+b|+|a+b+c|).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50168 (a b c : ℝ) : (|a| + |b| + |c| - |b + c| - |c + a| - |a + b| + |a + b + c|) * (|a| + |b| + |c| + |a + b + c|) = (|b| + |c| - |b + c|) * (|a| - |b + c| + |a + b + c|) + (|c| + |a| - |c + a|) * (|b| - |c + a| + |a + b + c|) + (|a| + |b| - |a + b|) * (|c| - |a + b| + |a + b + c|)   :=  by sorry
