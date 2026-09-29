-- Prove2me | Theorems.Thm_lean_workbook_plus_44870
-- name    : lean_workbook_plus_44870
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/fb406032-ff86-4d21-9bb7-24400fb690b9
-- statement:
--   Let $a$ , $b$ and $c$ be positive numbers. Prove that: $\frac{(a+b+c)^2}{ab+ac+bc}\geq\frac{a+b}{b+c}+\frac{b+c}{c+a}+\frac{c+a}{a+b}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44870 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 2 / (a * b + b * c + a * c) ≥ (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b)   :=  by sorry
