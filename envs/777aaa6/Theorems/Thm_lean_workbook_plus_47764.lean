-- Prove2me | Theorems.Thm_lean_workbook_plus_47764
-- name    : lean_workbook_plus_47764
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/95465187-39f4-4478-a056-5851b02eeb9b
-- statement:
--   Note that $\sum_{k=n}^{m} {k+n-2 \choose n-1} = {m+n-1 \choose n} - {2n-2 \choose n}$ by the Hockeystick identity applied twice. Likewise $\sum_{k=n}^{m} {k+n-2 \choose n-3} = {m+n-1 \choose n-2} - {2n-2 \choose n-2}$ . We have ${2n-2 \choose n} = {2n-2 \choose n-2}$ , so by subtracting these two, we get $s_{n+1,m} = {m+n-1 \choose n} - {m+n-1 \choose n-2}$ , as desired.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47764 : ∀ n m : ℕ, n ≤ m → ∑ k in Finset.Icc n m, (k + n - 2).choose n = (m + n - 1).choose n - (m + n - 1).choose (n - 2)   :=  by sorry
