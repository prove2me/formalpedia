-- Prove2me | Theorems.Thm_lean_workbook_plus_22802
-- name    : lean_workbook_plus_22802
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/4238f508-ae3c-4734-a2cc-d683512ddeb3
-- statement:
--   Let $ a, b$ and $ c$ be be positive real numbers such that $\frac{1}{a}+\frac{1}{b}+\frac{1}{c}=2 $ . Prove that $ (a-1) (b-1) (c-1) (abc-1)\le \frac{19}{64}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22802 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : 1 / a + 1 / b + 1 / c = 2) : (a - 1) * (b - 1) * (c - 1) * (a * b * c - 1) ≤ 19 / 64   :=  by sorry
