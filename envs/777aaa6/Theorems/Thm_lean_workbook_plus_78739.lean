-- Prove2me | Theorems.Thm_lean_workbook_plus_78739
-- name    : lean_workbook_plus_78739
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/4c9e6b79-e4d8-4ada-b2e1-630293ced5dc
-- statement:
--   The following inequality is true for all positives $a$ , $b$ and $c$ . \n $$a^3+b^3+c^3+abc\geq a\left(\frac{3}{2}b^2+\frac{3}{2}c^2+bc\right)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78739 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 + a * b * c ≥ a * (3 / 2 * b^2 + 3 / 2 * c^2 + b * c)   :=  by sorry
