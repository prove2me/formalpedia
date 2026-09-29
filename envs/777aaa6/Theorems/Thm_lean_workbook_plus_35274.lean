-- Prove2me | Theorems.Thm_lean_workbook_plus_35274
-- name    : lean_workbook_plus_35274
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/f0b70567-6739-4d6a-8eae-1a97cd50260b
-- statement:
--   Let $a,b,c $ be reals such that $a+b+c=2 $ . Prove that $$|a|-|b|-|c|\leq 2$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35274 (a b c : ℝ) (h : a + b + c = 2) :
  |a| - |b| - |c| ≤ 2   :=  by sorry
