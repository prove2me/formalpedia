-- Prove2me | Theorems.Thm_lean_workbook_plus_75903
-- name    : lean_workbook_plus_75903
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/56a741bb-2439-4acb-a537-dd1a36807c72
-- statement:
--   A convex sequence is a sequence of integers where each term (but first or last) is no greater than the arithmetic mean of the terms immediately before and after it. For example, the sequence 4,1,2,3 is convex because $1\leq \frac{4+2}2$ and $2 \leq \frac{1+3}2$ . How many convex sequences use each number in the set {1, 2, 3, 4, 5, 6, 7, 8} exactly once?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75903 {s: Set ℕ | ∃ f: ℕ → ℕ, Function.Bijective f ∧ ∀ n, (n > 0 ∧ n < 8) → f n ≤ (f (n-1) + f (n+1)) / 2} = {s: Set ℕ | ∃ f: ℕ → ℕ, Function.Bijective f ∧ ∀ n, (n > 0 ∧ n < 8) → f n ≤ (f (n-1) + f (n+1)) / 2}   :=  by sorry
