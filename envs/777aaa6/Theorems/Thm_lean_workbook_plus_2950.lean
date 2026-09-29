-- Prove2me | Theorems.Thm_lean_workbook_plus_2950
-- name    : lean_workbook_plus_2950
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/e6a5751d-c630-482e-ae47-c966353a938f
-- statement:
--   $(a+b+c)^3\geq\frac{9}{4}\cdot ((a+b)^2c+((b+c)^2a+(c+a)^2b) \iff 4(a^3+b^3+c^3)+3(a(b^2+c^2)+b(c^2+a^2)+c(a^2+b^2))\ge 30abc
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2950 (a b c : ℝ) :
  (a + b + c) ^ 3 ≥ (9 / 4) * (a * (b + c) ^ 2 + b * (c + a) ^ 2 + c * (a + b) ^ 2) ↔
    4 * (a ^ 3 + b ^ 3 + c ^ 3) + 3 * (a * (b ^ 2 + c ^ 2) + b * (c ^ 2 + a ^ 2) + c * (a ^ 2 + b ^ 2)) ≥
      30 * a * b * c   :=  by sorry
