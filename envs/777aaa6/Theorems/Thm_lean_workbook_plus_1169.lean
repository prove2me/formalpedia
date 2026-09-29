-- Prove2me | Theorems.Thm_lean_workbook_plus_1169
-- name    : lean_workbook_plus_1169
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/871313d9-51aa-4928-8545-015a12845db9
-- statement:
--   Let $ a,b,c>0$ . Prove that: \n\n $ \frac{4}{3}\cdot\left (\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}\right )+\sqrt[3]{\frac{abc}{(a+b)(b+c)(c+a)}}\geq \frac{5}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1169 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (4 / 3) * (a / (b + c) + b / (c + a) + c / (a + b)) + (abc / (a + b) / (b + c) / (c + a))^(1 / 3) ≥ 5 / 2   :=  by sorry
