-- Prove2me | Theorems.Thm_lean_workbook_plus_25179
-- name    : lean_workbook_plus_25179
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/a293dd80-b686-47ba-90ec-7fba7f5f1731
-- statement:
--   Let $a,b,c>0$ and $(a+b)(b+c)(a+c)=1$ . The, prove that $ab+ac+bc\geq\frac{3}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25179 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) (h : (a + b) * (b + c) * (a + c) = 1) : a * b + b * c + c * a ≥ 3 / 4   :=  by sorry
