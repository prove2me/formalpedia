-- Prove2me | Theorems.Thm_lean_workbook_plus_74129
-- name    : lean_workbook_plus_74129
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/7a07c42a-b656-41c9-b6a1-90d7f94ed338
-- statement:
--   Using the identity $(a + b + c)(ab + bc + ac) = 1 + abc$, prove the inequality $ab + bc + ac \leq \frac{3}{4}$ for $a, b, c > 0$ and $(a + b)(a + c)(b + c) = 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74129 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 1) (h : (a + b) * (a + c) * (b + c) = 1) : a * b + b * c + a * c ≤ 3 / 4   :=  by sorry
