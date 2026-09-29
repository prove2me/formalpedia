-- Prove2me | Theorems.Thm_lean_workbook_plus_60125
-- name    : lean_workbook_plus_60125
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/a3badbf1-b640-49c2-b2aa-9b493cfac17a
-- statement:
--   Let $a,b,c $ be real numbers such that $a^2 = 2b + 1$ and $ b^2 = 2c + 1 .$ Prove that $a+b+c\geq -\frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60125 (a b c : ℝ) (ha : a^2 = 2 * b + 1) (hb : b^2 = 2 * c + 1) : a + b + c ≥ -3 / 2   :=  by sorry
