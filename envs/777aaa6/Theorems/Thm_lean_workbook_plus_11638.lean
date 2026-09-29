-- Prove2me | Theorems.Thm_lean_workbook_plus_11638
-- name    : lean_workbook_plus_11638
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/80028b7d-7e1c-47b5-9983-b974f6e69f02
-- statement:
--   Prove that $\binom{2}{2}+\binom{3}{2}+\binom{4}{2}+\ldots+\binom{n+1}{2}=\binom{n+2}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11638 (n : ℕ) : ∑ k in Finset.Icc 2 (n+1), (Nat.choose k 2) = Nat.choose (n+2) 3   :=  by sorry
