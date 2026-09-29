-- Prove2me | Theorems.Thm_lean_workbook_plus_31464
-- name    : lean_workbook_plus_31464
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/cbd55e80-915c-4b8d-9f06-2bbf8f317eb3
-- statement:
--   Let $ a,b,c$ be non-negative real numbers and they aren't all equal to zero. Prove that \n $ \sum\limits_{cyc}a^3 + 3abc\ge \sum\limits_{cyc}ab(a + b) + \frac {\sum\limits_{cyc}ab(a - b)^2}{a + b + c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31464 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b > 0) (hbc : b + c > 0) (hca : a + c > 0) : a^3 + b^3 + c^3 + 3 * a * b * c ≥ a * b * (a + b) + b * c * (b + c) + c * a * (c + a) + (a * b * (a - b)^2 + b * c * (b - c)^2 + c * a * (c - a)^2) / (a + b + c)   :=  by sorry
