-- Prove2me | Theorems.Thm_lean_workbook_plus_81298
-- name    : lean_workbook_plus_81298
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/0800ad6a-fb51-4cf3-8eca-09eba65d56ef
-- statement:
--   Prove that $\max(a,b)=\dfrac{a+b+|a-b|}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81298 (a b : ℝ) : max a b = (a + b + |a - b|) / 2   :=  by sorry
