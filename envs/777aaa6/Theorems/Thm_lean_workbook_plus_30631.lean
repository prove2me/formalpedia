-- Prove2me | Theorems.Thm_lean_workbook_plus_30631
-- name    : lean_workbook_plus_30631
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/a4ac0fcf-d118-4f53-a7d7-e1f76f87dfbe
-- statement:
--   If $a+b+c+d=6$ for positive $a,b,c,d,$ find the maximum possible value of $ab+bc+cd+da.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30631 (a b c d : ℝ) (h : a + b + c + d = 6) : a * b + b * c + c * d + d * a ≤ 9   :=  by sorry
