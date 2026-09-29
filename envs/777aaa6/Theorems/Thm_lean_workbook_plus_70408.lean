-- Prove2me | Theorems.Thm_lean_workbook_plus_70408
-- name    : lean_workbook_plus_70408
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/391881ff-14de-4111-b361-83e4d4e16e1f
-- statement:
--   Let $a, b$ and $c$ be positive real numbers. Prove that $$ \big(\frac{a}{a+b+c}+\frac{2}{3}\big) \big(\frac{b}{a+b+c}+\frac{2}{3}\big) \big(\frac{c}{a+b+c}+\frac{2}{3}\big)\le 1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70408 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (a + b + c) + 2 / 3) * (b / (a + b + c) + 2 / 3) * (c / (a + b + c) + 2 / 3) ≤ 1   :=  by sorry
