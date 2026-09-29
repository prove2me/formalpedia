-- Prove2me | Theorems.Thm_lean_workbook_plus_18955
-- name    : lean_workbook_plus_18955
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/b3bb5839-8861-4ec7-b2df-44ffd638b733
-- statement:
--   Let $a, b$ be real numbers that $|a|<1$ and $|b|<1$ . Prove that $\left|\frac{a+b}{1+ab}\right|<1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18955 (a b : ℝ) (ha : abs a < 1) (hb : abs b < 1) : abs (a + b) / (1 + a * b) < 1   :=  by sorry
