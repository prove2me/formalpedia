-- Prove2me | Theorems.Thm_lean_workbook_plus_41132
-- name    : lean_workbook_plus_41132
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/e9634fa3-406e-4366-bbee-563ab93eb9c7
-- statement:
--   Show that $\sum_{m=0}^{500} \ (-1)^m \binom{1000}{2m} = 2^{500}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41132 (n : ℕ) : ∑ m in Finset.range (500 + 1), (-1 : ℤ)^m * choose 1000 (2*m) = 2^500   :=  by sorry
