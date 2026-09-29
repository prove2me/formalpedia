-- Prove2me | Theorems.Thm_lean_workbook_plus_69297
-- name    : lean_workbook_plus_69297
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/6761a3c3-642e-401a-abb3-9f57552ac240
-- statement:
--   Prove that for all positive real numbers $a,b,c$ the following inequality holds: $(a+b+c)\left(\frac1a+\frac1b+\frac1c\right)\ge\frac{2(a^2+b^2+c^2)}{ab+bc+ca}+7$ and determine all cases of equality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69297 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 2 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + a * c) + 7   :=  by sorry
