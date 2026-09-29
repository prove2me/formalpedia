-- Prove2me | Theorems.Thm_lean_workbook_plus_11360
-- name    : lean_workbook_plus_11360
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/ac736b45-8a1e-488b-85f0-84e2db08b872
-- statement:
--   For non-negative reals $ a,$ $ b$ and $ c$ we obtain: $ \sum_{cyc}\frac{1}{a+2}\leq\frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11360 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 1 / (a + 2) + 1 / (b + 2) + 1 / (c + 2) ≤ 3 / 2   :=  by sorry
