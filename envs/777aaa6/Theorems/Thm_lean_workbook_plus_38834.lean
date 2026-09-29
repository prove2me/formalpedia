-- Prove2me | Theorems.Thm_lean_workbook_plus_38834
-- name    : lean_workbook_plus_38834
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/9f0dbaeb-47c5-4ed2-92d2-369afa7f9981
-- statement:
--   Prove the inequality $ \dbinom {n}{k} \leq \dbinom {n}{[n/2]}$ where $k=0,1,...,n$ , and $n$ is a natural number.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38834 (n k : ℕ) (h₀ : k ≤ n) : choose n k ≤ choose n (n/2)   :=  by sorry
