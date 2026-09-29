-- Prove2me | Theorems.Thm_lean_workbook_plus_71573
-- name    : lean_workbook_plus_71573
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/04128092-12ba-4451-b75e-03c7e6aacc63
-- statement:
--   Prove that $ \displaystyle\prod_{k = 1}^{n - 1} \sin \frac {k \pi}{n} = \frac {n}{2^{n - 1}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71573 : ∀ n : ℕ, ∏ k in Finset.range (n - 1), Real.sin (k * Real.pi / n) = n / 2 ^ (n - 1)   :=  by sorry
