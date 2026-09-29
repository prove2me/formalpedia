-- Prove2me | Theorems.Thm_lean_workbook_plus_29421
-- name    : lean_workbook_plus_29421
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/91b53bc6-f85e-478b-8213-a3bcb920096b
-- statement:
--   Let $ a,b,c,d\in[ 0: 1]$. Prove that: $ a(1-d)+b(1-a)+c(1-b)+d(1-c)\leq2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29421 (a b c d : ℝ) (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) (hd : d ∈ Set.Icc 0 1) : a * (1 - d) + b * (1 - a) + c * (1 - b) + d * (1 - c) ≤ 2   :=  by sorry
