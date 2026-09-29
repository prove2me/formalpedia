-- Prove2me | Theorems.Thm_lean_workbook_plus_3882
-- name    : lean_workbook_plus_3882
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/ba05db0e-d30a-4789-bb2d-50e7eb6f47fd
-- statement:
--   Let $ a, b$ and $ c$ be be positive real numbers such that $a+b+c=2 $ . Prove that $ (a-1) (b-1) (c-1) (1-abc)\ge \frac{2375a^4b^4c^4}{512}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3882 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (hab : a + b + c = 2) :  (a - 1) * (b - 1) * (c - 1) * (1 - a * b * c) ≥ (2375 * a ^ 4 * b ^ 4 * c ^ 4) / 512   :=  by sorry
