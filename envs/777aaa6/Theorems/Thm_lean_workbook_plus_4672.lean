-- Prove2me | Theorems.Thm_lean_workbook_plus_4672
-- name    : lean_workbook_plus_4672
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/6ebd459c-c58c-4a93-ac92-48d1b8b48b86
-- statement:
--   Observe that there are $n+1$ sequences in the form of $FF ... FSS ... S$ . There are $2^n$ sequences of $F$ 's and $S$ 's, so the sought number is $2^n - (n+1) + 1 = 2^n - n$ . (The last $+1$ is from counting $FF ... F$ ; we haven't counted that in $2^n - (n+1)$ .)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4672 ∀ n : ℕ, (∑ k in Finset.range (n+1), (Nat.choose n k)) - (n+1) + 1 = 2^n - n   :=  by sorry
