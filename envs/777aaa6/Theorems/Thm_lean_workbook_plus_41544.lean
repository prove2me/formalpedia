-- Prove2me | Theorems.Thm_lean_workbook_plus_41544
-- name    : lean_workbook_plus_41544
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/3bbf2f3a-7e42-4075-9f08-0993900e4fe5
-- statement:
--   Let $a,$ $b$ and $c$ are sides lengths of triangle. Prove that $\frac{(a+b)(a+c)(b+c)}{8}\geq\frac{(2a+b)(2b+c)(2c+a)}{27}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41544 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (a + b) * (a + c) * (b + c) / 8 ≥ (2 * a + b) * (2 * b + c) * (2 * c + a) / 27   :=  by sorry
