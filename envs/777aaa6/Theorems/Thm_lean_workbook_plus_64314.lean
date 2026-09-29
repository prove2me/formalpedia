-- Prove2me | Theorems.Thm_lean_workbook_plus_64314
-- name    : lean_workbook_plus_64314
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/eee7155a-76ae-4734-9262-904792aedbe0
-- statement:
--   Prove that for all positive real numbers: \n $2\left( \frac{1}{ab}+\frac{1}{bc}+\frac{1}{ca}\right) \le \frac{2}{3}\left(\frac{1}{a}+\frac{1}{b}+\frac{1}{c}\right)^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64314 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : 2 * (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) ≤ (2 / 3) * (1 / a + 1 / b + 1 / c) ^ 2   :=  by sorry
