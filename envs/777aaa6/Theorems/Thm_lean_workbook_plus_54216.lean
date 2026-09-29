-- Prove2me | Theorems.Thm_lean_workbook_plus_54216
-- name    : lean_workbook_plus_54216
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/941278e6-34e1-44f5-83bc-bfb118f9a112
-- statement:
--   Using $\binom{n}{k}=\binom{n}{n-k}$ it suffices to show that $\binom{n}{n}+\binom{n+1}{n}+\binom{n+2}{n}+\cdots{+\binom{n+r}{n}}=\binom{n+r+1}{n+1}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54216 (n r : ℕ) : ∑ i in Finset.range (r+1), (n+i).choose n = (n+r+1).choose (n+1)   :=  by sorry
