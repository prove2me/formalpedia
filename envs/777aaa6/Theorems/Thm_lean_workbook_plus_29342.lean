-- Prove2me | Theorems.Thm_lean_workbook_plus_29342
-- name    : lean_workbook_plus_29342
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/2cf7d9fb-d8a6-43b9-951c-9a7e0d85069f
-- statement:
--   Consider having to pick $r$ objects from a total of $n$ . This can be split up into two cases. Either the first object is chosen, or it is not. Now assume the first object is chosen. There are clearly $\binom{n-1}{r-1}$ ways to do this. If the first object isn't chosen, there are $\binom{n-1}{r}$ ways to do this. Another way to count this is to obviously just do $\binom{n}{r}$ . Thus we have that $\binom{n-1}{r-1}+\binom{n-1}{r}=\binom{n}{r},$ and we are done. $\blacksquare$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29342  (n r : ℕ)
  (h₀ : 0 < n ∧ 0 < r)
  (h₁ : r ≤ n) :
  Nat.choose n r = Nat.choose (n - 1) (r - 1) + Nat.choose (n - 1) r   :=  by sorry
