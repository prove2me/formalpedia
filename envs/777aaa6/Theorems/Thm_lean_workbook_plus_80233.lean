-- Prove2me | Theorems.Thm_lean_workbook_plus_80233
-- name    : lean_workbook_plus_80233
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/e0c51eab-fe44-4137-b22c-606758f5379c
-- statement:
--   Let a,b,c follow that: \n $a+b+c>0$ \n $ab+bc+ca>0$ \n $abc>0$ \nProve that: a,b,c>0
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80233 (a b c : ℝ) (h1 : a + b + c > 0) (h2 : a * b + b * c + c * a > 0) (h3 : a * b * c > 0) : a > 0 ∧ b > 0 ∧ c > 0   :=  by sorry
