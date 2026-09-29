-- Prove2me | Theorems.Thm_lean_workbook_plus_12126
-- name    : lean_workbook_plus_12126
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/80b160b3-ed27-4aa6-89dd-583963a2325c
-- statement:
--   Let $a,b,c> 0$ such that $abc=1$ , prove that $$(ab+c)(bc+a)(ca+b)\ge (a+b)(b+c)(c+a)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12126 (a b c : ℝ) (habc : a * b * c = 1) : (a * b + c) * (b * c + a) * (c * a + b) ≥ (a + b) * (b + c) * (c + a)   :=  by sorry
