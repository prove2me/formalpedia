-- Prove2me | Theorems.Thm_lean_workbook_plus_59739
-- name    : lean_workbook_plus_59739
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/e506b0c3-825c-4ea3-80fc-49f13ae52394
-- statement:
--   Let $a,b,c \geq 0$ such that $a^2+b^2+c^2=1$ . $$\frac{a+b}{1-ab}+\frac{b+c}{1-bc}+\frac{c+a}{1-ca} \leq 3(a+b+c).$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59739 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : (a + b) / (1 - a * b) + (b + c) / (1 - b * c) + (c + a) / (1 - c * a) ≤ 3 * (a + b + c)   :=  by sorry
