-- Prove2me | Theorems.Thm_lean_workbook_plus_27630
-- name    : lean_workbook_plus_27630
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/e4e68c58-ce6a-4633-9e6b-b593df7331f0
-- statement:
--   Let $ a,b,c $ be positive real numbers .Prove that $( a+b+\dfrac{1}{2})(b+c+\dfrac{1}{2})(c+a+\dfrac{1}{2})\geq (2a+\dfrac{1}{2})(2b+\dfrac{1}{2})(2c+\dfrac{1}{2}) .$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27630 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + 1 / 2) * (b + c + 1 / 2) * (c + a + 1 / 2) ≥ (2 * a + 1 / 2) * (2 * b + 1 / 2) * (2 * c + 1 / 2)   :=  by sorry
