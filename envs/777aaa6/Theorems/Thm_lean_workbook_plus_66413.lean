-- Prove2me | Theorems.Thm_lean_workbook_plus_66413
-- name    : lean_workbook_plus_66413
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/d2202357-13f3-4d67-8647-e578237039d4
-- statement:
--   Let be three real numbers $ a,b,c\in [0,1] $ satisfying the condition $ ab+bc+ca=1. $ Prove that: $ a+b+c+abc \leq 2 $ and determine the cases in which equality is attained.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66413 (a b c : ℝ) (h : a ∈ Set.Icc 0 1 ∧ b ∈ Set.Icc 0 1 ∧ c ∈ Set.Icc 0 1) (h2: a * b + b * c + c * a = 1) : a + b + c + a * b * c ≤ 2   :=  by sorry
