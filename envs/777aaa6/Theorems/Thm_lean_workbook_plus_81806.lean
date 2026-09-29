-- Prove2me | Theorems.Thm_lean_workbook_plus_81806
-- name    : lean_workbook_plus_81806
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/9bb29a40-452b-4e28-a116-e9a0b2002cef
-- statement:
--   Let $a,b,c >0 $ and $a+b+c=\frac{1}{a}+\frac{1}{b}+\frac{1}{c} .$ Prove that $ab+bc+ca\geq 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81806 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a + b + c = 1 / a + 1 / b + 1 / c) : a * b + b * c + c * a ≥ 3   :=  by sorry
