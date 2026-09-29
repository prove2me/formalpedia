-- Prove2me | Theorems.Thm_lean_workbook_plus_67663
-- name    : lean_workbook_plus_67663
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/014b2a95-48aa-4830-91e7-ae39512b0093
-- statement:
--   Prove that for positive numbers $a$, $b$, and $c$ with $a^2 + b^2 + c^2 = 1$, the following inequality holds:\n$$(a^2 + b^2 + c^2)(\frac{1}{a^2} + \frac{1}{b^2} + \frac{1}{c^2}) \geq 3 + \frac{2(a^3 + b^3 + c^3)}{abc}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67663 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :  (a^2 + b^2 + c^2) * (1 / a^2 + 1 / b^2 + 1 / c^2) ≥ 3 + (2 * (a^3 + b^3 + c^3)) / (a * b * c)   :=  by sorry
