-- Prove2me | Theorems.Thm_lean_workbook_plus_73043
-- name    : lean_workbook_plus_73043
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/41e927d0-e845-4a15-a667-11ab18654ee7
-- statement:
--   We prove that the set of all primes dividing at least one term of the sequence $a_n=1!+ \dots + n!$ is infinite. Assume to the contrary. Let this set be $S=\{p_1, \dots, p_k\}$ for some $k \ge 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73043 : Set.Infinite { p : ℕ | ∃ n : ℕ, p ∣ (∑ i in Finset.range n, i!)}   :=  by sorry
