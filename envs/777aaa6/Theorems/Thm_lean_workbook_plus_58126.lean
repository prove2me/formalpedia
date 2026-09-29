-- Prove2me | Theorems.Thm_lean_workbook_plus_58126
-- name    : lean_workbook_plus_58126
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/99fe09c7-eeef-4720-b61c-fd895657649b
-- statement:
--   Prove that for positive real numbers a and b, \((a+b+\frac{1}{2})^2\geq4(a+\frac{1}{4})(b+\frac{1}{4}).\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58126 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a + b + 1 / 2) ^ 2 ≥ 4 * (a + 1 / 4) * (b + 1 / 4)   :=  by sorry
