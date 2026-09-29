-- Prove2me | Theorems.Thm_lean_workbook_plus_6687
-- name    : lean_workbook_plus_6687
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/a6d99ba6-7db9-47ec-b91b-0f37aafb1647
-- statement:
--   Prove that $a>0,b>0,c>0$ and $ab+bc+ca+2abc=1\Longrightarrow 1+2(a+b+c)\geqq 32abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6687 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) (h : a * b + b * c + c * a + 2 * a * b * c = 1) : 1 + 2 * (a + b + c) ≥ 32 * a * b * c   :=  by sorry
