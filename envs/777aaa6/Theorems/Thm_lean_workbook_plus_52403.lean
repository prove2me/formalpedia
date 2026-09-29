-- Prove2me | Theorems.Thm_lean_workbook_plus_52403
-- name    : lean_workbook_plus_52403
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/dfe75be1-5165-4074-a21b-1b86b44d69fd
-- statement:
--   Prove that for all positive real numbers: \n $2\left( \frac{1}{ab}+\frac{1}{bc}+\frac{1}{ca}\right) \le \frac{2}{3}\left(\frac{1}{a}+\frac{1}{b}+\frac{1}{c}\right)^{2}$ \n \n Use this \n $$(a+b+c)^2\geq 3(ab+bc+ca)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52403 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) ≤ (2 / 3) * (1 / a + 1 / b + 1 / c)^2   :=  by sorry
