-- Prove2me | Theorems.Thm_lean_workbook_plus_53015
-- name    : lean_workbook_plus_53015
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/636ff00f-e3b3-4bf0-a139-e5e92d9f0d0b
-- statement:
--   $\binom{n}{0} - \binom{n}{1} +\binom{n}{2} - ... +(-1)^{n} \binom{n}{n} = (1-1)^{n} = 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53015 : ∀ n : ℕ, ∑ k in Finset.range (n+1), (-1 : ℤ)^k * choose n k = 0   :=  by sorry
