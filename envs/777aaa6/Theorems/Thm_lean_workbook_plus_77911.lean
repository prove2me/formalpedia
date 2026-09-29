-- Prove2me | Theorems.Thm_lean_workbook_plus_77911
-- name    : lean_workbook_plus_77911
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/e05a4153-0a8e-4924-b081-9707ea1e8957
-- statement:
--   Prove that the sum of the first n odd numbers is $n^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77911 (n : ℕ) : ∑ k in (Finset.range n), (2 * k + 1) = n^2   :=  by sorry
