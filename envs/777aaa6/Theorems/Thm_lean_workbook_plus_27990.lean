-- Prove2me | Theorems.Thm_lean_workbook_plus_27990
-- name    : lean_workbook_plus_27990
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/a6e15b2a-a849-4898-8834-e615b0de70f6
-- statement:
--   a,b,c are real numbers such that $a+b+c=0$\nprove that:\n\n $ (a^2+b^2+c^2)^3 \geq 27a^2b^2c^2+ (a-b)^2(b-c)^2(c-a)^2 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27990 (a b c : ℝ) (h : a + b + c = 0) :
  (a^2 + b^2 + c^2)^3 ≥ 27 * a^2 * b^2 * c^2 + (a - b)^2 * (b - c)^2 * (c - a)^2   :=  by sorry
