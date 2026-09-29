-- Prove2me | Theorems.Thm_lean_workbook_plus_40812
-- name    : lean_workbook_plus_40812
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/0a5cd8c2-33c1-4b10-ad54-9902775064ff
-- statement:
--   Prove that \(\frac{a}{b} + \frac{b}{c} + \frac{c}{a} = \frac{a^2}{ab} + \frac{b^2}{bc} + \frac{c^2}{ac} \geq \frac{(a+b+c)^2}{ab+bc+ca}\) where \( a,b,c > 0 \).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40812 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + b / c + c / a = a^2 / (a * b) + b^2 / (b * c) + c^2 / (c * a) ∧ a / b + b / c + c / a ≥ (a + b + c)^2 / (a * b + b * c + c * a)   :=  by sorry
