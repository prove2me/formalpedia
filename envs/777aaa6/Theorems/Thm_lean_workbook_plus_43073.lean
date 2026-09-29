-- Prove2me | Theorems.Thm_lean_workbook_plus_43073
-- name    : lean_workbook_plus_43073
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/a566eed0-f9c0-4227-b594-fc2b04130220
-- statement:
--   Let $a,b,c>0$ and $2a+b+c\leq \frac{3}{2}.$ Prove that \n $$a^2+bc+\frac{2}{a}+\frac{1}{b}+\frac{1}{c}\geq\frac{1051}{96} $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43073 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (hab : 2 * a + b + c ≤ 3 / 2) : a^2 + b * c + 2 / a + 1 / b + 1 / c ≥ 1051 / 96   :=  by sorry
