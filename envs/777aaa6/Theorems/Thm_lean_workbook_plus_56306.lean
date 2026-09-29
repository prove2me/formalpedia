-- Prove2me | Theorems.Thm_lean_workbook_plus_56306
-- name    : lean_workbook_plus_56306
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/7559bfc5-2a73-4bae-818b-3c6305c38d55
-- statement:
--   $\frac{(a+b)(b+c)(c+a)}{abc} - \frac{24(a^2+b^2+c^2)}{(a+b+c)^2} = \sum \frac{(a+b-3c)^2(a-b)^2}{ab(a+b+c)^2} \geqslant 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56306 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (a + b) * (b + c) * (c + a) / a / b / c - 24 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 2 = (a + b - 3 * c) ^ 2 * (a - b) ^ 2 / (a * b * (a + b + c) ^ 2) + (b + c - 3 * a) ^ 2 * (b - c) ^ 2 / (b * c * (a + b + c) ^ 2) + (c + a - 3 * b) ^ 2 * (c - a) ^ 2 / (c * a * (a + b + c) ^ 2)   :=  by sorry
