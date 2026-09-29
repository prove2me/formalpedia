-- Prove2me | Theorems.Thm_lean_workbook_plus_11626
-- name    : lean_workbook_plus_11626
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/ec027256-c5de-4501-a905-589aeb43b76f
-- statement:
--   Prove the identity $\binom{n}{r}=\binom{n}{n-r}$ using Bijection Principle.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11626 (n r : ℕ) (h₁ : n = r + (n - r)) (h₂ : n - r = n - r) : choose n r = choose n (n - r)   :=  by sorry
