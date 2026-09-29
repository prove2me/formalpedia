-- Prove2me | Theorems.Thm_lean_workbook_plus_1479
-- name    : lean_workbook_plus_1479
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/10e95a6b-abce-483e-b80a-0b3828459f61
-- statement:
--   We have $\frac{a}{b},\frac{b}{c},\frac{c}{a}$ are all positive rational numbers and all of them are root of equation $x^3-\Big( \frac{a}{b}+\frac{b}{c}+\frac{c}{a}\Big) x^2 +\Big( \frac{a}{c}+\frac{c}{b}+\frac{b}{a} \Big) x-1=0$ which all coefficient are integers
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1479 (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a * b * c ≠ 0) : (a / b : ℚ) ^ 3 - (a / b + b / c + c / a) * (a / b) ^ 2 + (a / c + c / b + b / a) * (a / b) - 1 = 0   :=  by sorry
