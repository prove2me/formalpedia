-- Prove2me | Theorems.Thm_lean_workbook_plus_41048
-- name    : lean_workbook_plus_41048
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/74ebe607-ed31-4415-86e5-f5f985357c31
-- statement:
--   Given $a,b,c \in \mathbb{R}^+$ prove that \n $\frac{4}{3}( \frac{a}{b+c}+\frac{b}{a+c}+\frac{c}{a+b})$ + $\sqrt[3]{\frac{abc}{(a+b)(b+c)(a+c)}}$ $\geq$ $\frac{5}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41048 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (4 / 3 * (a / (b + c) + b / (a + c) + c / (a + b))) + (abc / (a + b) / (b + c) / (a + c))^(1 / 3) ≥ 5 / 2   :=  by sorry
