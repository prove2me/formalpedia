-- Prove2me | Theorems.Thm_lean_workbook_plus_39847
-- name    : lean_workbook_plus_39847
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/6e4d39c3-8412-4127-ac09-9cd9dc0946c8
-- statement:
--   Let $n$ be the least positive integer greater than $1000$ for which $\gcd(63, n+120) =21\quad \text{and} \quad \gcd(n+63, 120)=60$. What is the sum of the digits of $n$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39847 (n : ℕ) (hn : 1000 < n) (h1 : Nat.gcd (63) (n + 120) = 21) (h2 : Nat.gcd (n + 63) (120) = 60) : n = 1890 ∧ (Nat.digits 10 n).sum = 18   :=  by sorry
