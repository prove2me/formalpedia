-- Prove2me | Theorems.Thm_lean_workbook_plus_76132
-- name    : lean_workbook_plus_76132
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/b3eb2217-2930-4cf9-afaa-7abf33248c73
-- statement:
--   Let $a$ , $b$ and $c$ be distinct positive real numbers. Prove that\n\n $$\frac{a^3}{(b-c)^2}+ \frac{b^3}{(c-a)^2}+ \frac{c^3}{(a-b)^2}=a+b+c+\left(\frac{a}{b-c}+ \frac{b}{c-a}+ \frac{c}{a-b} \right)\left(\frac{a^2}{b-c}+ \frac{b^2}{c-a}+ \frac{c^2}{a-b} \right)$$\nLet $a_1,a_2,\cdots,a_n (n\ge 2)$ be distinct non-negative numbers.Prove that $$\frac{a^3_1}{(a_2-a_3)^2}+\frac{a^3_2}{(a_3-a_4)^2}+\cdots+\frac{a^3_{n-1}}{(a_n-a_1)^2}+\frac{a^3_n}{(a_1-a_2)^2}\geq a_1+a_2+\cdots +a_n.$$ (Jichen) p/6748080023\n\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76132 (a b c : ℝ) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) : a^3 / (b - c)^2 + b^3 / (c - a)^2 + c^3 / (a - b)^2 = a + b + c + (a / (b - c) + b / (c - a) + c / (a - b)) * (a^2 / (b - c) + b^2 / (c - a) + c^2 / (a - b))   :=  by sorry
