-- Prove2me | Theorems.Thm_lean_workbook_plus_11115
-- name    : lean_workbook_plus_11115
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/00d947c3-7d7a-4b2a-91aa-f7f45bc395d1
-- statement:
--   $(x+n)^3=x^3+m$ and so $3nx^2+3n^2x+n^3-m=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11115 (x n m : ℤ) (h₁ : (x + n) ^ 3 = x ^ 3 + m) : 3 * n * x ^ 2 + 3 * n ^ 2 * x + n ^ 3 - m = 0   :=  by sorry
