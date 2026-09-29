-- Prove2me | Theorems.Thm_lean_workbook_plus_21689
-- name    : lean_workbook_plus_21689
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/a7ee9033-906d-459f-acc3-688661b5f9d4
-- statement:
--   Prove that if $a,b,c>0$ then \n $ \frac{1}{2} + \frac{a^2+b^2+c^2}{ab+bc+ca} \geq \frac{a}{b+c} +\frac{b}{c+a} +\frac{c}{a+b} \quad (1) $\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21689 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / 2 + (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) ) ≥ a / (b + c) + b / (c + a) + c / (a + b)   :=  by sorry
