-- Prove2me | Theorems.Thm_lean_workbook_plus_44214
-- name    : lean_workbook_plus_44214
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/d0496d00-7774-4365-a974-1493ef0f8e2f
-- statement:
--   Given $a, b, c > 0$ and $a + b + c = \frac{1}{a} + \frac{1}{b} + \frac{1}{c}$, prove that $bc + ac + ab + abc \geq 4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44214 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) (h : a + b + c = 1 / a + 1 / b + 1 / c) : b * c + a * c + a * b + a * b * c ≥ 4   :=  by sorry
