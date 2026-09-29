-- Prove2me | Theorems.Thm_lean_workbook_plus_60864
-- name    : lean_workbook_plus_60864
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/5265b99b-dfdb-4287-984d-df047b3069ef
-- statement:
--   Let a,b,c be real numbers such that $a+b+c=0$ . Prove that $\ (|a|+|b|+|c|)^2\geqq 2(a^2+b^2+c^2).$ When does equality holds?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60864 (a b c : ℝ) (h : a + b + c = 0) :
  (|a| + |b| + |c|) ^ 2 ≥ 2 * (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
