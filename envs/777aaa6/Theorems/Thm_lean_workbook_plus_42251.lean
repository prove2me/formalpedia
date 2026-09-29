-- Prove2me | Theorems.Thm_lean_workbook_plus_42251
-- name    : lean_workbook_plus_42251
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/edf43657-818a-418c-916a-697d1633e6ac
-- statement:
--   Prove that $e^x > \frac{2x}{x^2 + 1}$ for $x \in \mathbb{R}^+$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42251 (x : ℝ) (hx : 0 < x) : exp x > 2 * x / (x ^ 2 + 1)   :=  by sorry
