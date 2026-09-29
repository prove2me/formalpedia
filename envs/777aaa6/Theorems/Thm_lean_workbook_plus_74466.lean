-- Prove2me | Theorems.Thm_lean_workbook_plus_74466
-- name    : lean_workbook_plus_74466
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/8c283381-1339-461f-a33a-3e3100c3e00a
-- statement:
--   We claim the expression to compute is $\sum_{i=0}^{n-2}\dbinom{n}{i}\dbinom{n}{i+2} = \sum_{k=0}^{n-2} \binom {n} {n-k} \binom {n} {k+2} =$ $ \sum_{k=0}^{n-2} \binom {n} {k} \binom {n} {n-k-2} = \binom {2n} {n+2} = \binom {2n} {n-2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74466 : ∀ n : ℕ, n > 2 → ∑ k in Finset.range (n-2), (Nat.choose n k)*(Nat.choose n (k+2)) = (Nat.choose (2*n) (n+2))   :=  by sorry
