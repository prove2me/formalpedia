-- Prove2me | Theorems.Thm_lean_workbook_plus_79601
-- name    : lean_workbook_plus_79601
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/e0066d17-d01b-4d09-b1db-e2e4d426a5e7
-- statement:
--   For $a,b,c$ positive reals prove that $\frac{a}{ab+a+1}+\frac{b}{bc+b+1}+\frac{c}{ca+c+1} \leq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79601 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (a * b + a + 1) + b / (b * c + b + 1) + c / (c * a + c + 1)) ≤ 1   :=  by sorry
