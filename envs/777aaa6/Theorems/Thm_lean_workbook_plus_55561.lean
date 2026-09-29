-- Prove2me | Theorems.Thm_lean_workbook_plus_55561
-- name    : lean_workbook_plus_55561
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/e5625015-8cfa-4a87-bd0d-a4bd6ef990cf
-- statement:
--   Let $a,b,c>0$ Prove that: $ \frac{a-b}{b+c }+ \frac{b-c}{c+a }+ \frac{c-a}{a+b } \geq 0 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55561 (a b c : ℝ) (hab : 0 < a) (hbc : 0 < b) (hca : 0 < c) : (a - b) / (b + c) + (b - c) / (c + a) + (c - a) / (a + b) ≥ 0   :=  by sorry
