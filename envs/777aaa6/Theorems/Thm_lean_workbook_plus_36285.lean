-- Prove2me | Theorems.Thm_lean_workbook_plus_36285
-- name    : lean_workbook_plus_36285
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/45a716e4-4b25-4911-b995-675d9956ab83
-- statement:
--   Let k be an odd positive integer \\(\\ge3\\) . Prove that there exists distinct positive integers \\(a_{1},a_{2},a_{3},...a_{k}\\ge2\\) so that \\(\\sum_{i=1}^{k}\\frac{1}{a_{k}}=1\\) .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36285 (k : ℕ) (hk : 3 ≤ k) (hk' : Odd k) : ∃ (a : ℕ → ℕ), (∀ i, 2 ≤ a i ∧ ∀ i, a i ≠ a j) ∧ ∑ i in Finset.range k, (1 / a i) = 1   :=  by sorry
