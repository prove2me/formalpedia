-- Prove2me | Theorems.Thm_lean_workbook_plus_57898
-- name    : lean_workbook_plus_57898
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/519f42e5-1590-4511-8dd4-3adfd3e2d080
-- statement:
--   Prove the formula for the sum of the squares of the first n natural numbers: $1^2 + 2^2 + \ldots + n^2 = \dfrac{n(n + 1)(2n + 1)}{6}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57898 : ∀ n : ℕ, (∑ i in Finset.range n, i ^ 2) = n * (n + 1) * (2 * n + 1) / 6   :=  by sorry
