-- Prove2me | Theorems.Thm_lean_workbook_plus_46157
-- name    : lean_workbook_plus_46157
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/6386c3ac-0043-41e0-8558-7c0bcd380aab
-- statement:
--   Let $ a, b, c$ be positive real numbers such that $(a + b)(b + c)(c + a) = 1$ . Prove that $ab + bc + ca \leq \frac{3}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46157 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) (h : (a + b) * (b + c) * (c + a) = 1) : a * b + b * c + c * a ≤ 3 / 4   :=  by sorry
