-- Prove2me | Theorems.Thm_lean_workbook_plus_23983
-- name    : lean_workbook_plus_23983
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/0b17606f-867d-4411-9bc0-770133471127
-- statement:
--   Let $a,b,c>0 $ and $ abc=1$ . Prove that \n $$\dfrac{1}{9}-\dfrac{a}{(a+2)^2} \geq \dfrac{1}{9\left(a^2+a+1\right)}-\dfrac{1}{27}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23983 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : 1 / 9 - a / (a + 2) ^ 2 ≥ 1 / (9 * (a ^ 2 + a + 1)) - 1 / 27   :=  by sorry
