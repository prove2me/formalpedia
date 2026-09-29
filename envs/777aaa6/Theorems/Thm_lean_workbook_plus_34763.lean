-- Prove2me | Theorems.Thm_lean_workbook_plus_34763
-- name    : lean_workbook_plus_34763
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/0273b25d-bc2c-4208-b44b-5c13035a06c3
-- statement:
--   Let $a,b,c$ be positive real numbers such that $\frac{1}{a+b} + \frac{1}{b+c} + \frac{1}{c+a}=\frac{2}{3}. $ Prove that \n\n $$a+b+c+2\geq \frac{560}{729}abc$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34763 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) = 2 / 3) : a + b + c + 2 ≥ 560 / 729 * a * b * c   :=  by sorry
