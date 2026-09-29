-- Prove2me | Theorems.Thm_lean_workbook_plus_21823
-- name    : lean_workbook_plus_21823
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/aabfdf98-afe7-4d0c-a0cc-34bcbb64d9ec
-- statement:
--   Let a,b,c positive integers such that :abc=1. prove that: \n $\frac{1}{a+b+1}+\frac{1}{b+c+1}+\frac{1}{c+a+1}\leq{1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21823 (a b c : ℕ) (habc : a * b * c = 1) : 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) ≤ 1   :=  by sorry
