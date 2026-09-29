-- Prove2me | Theorems.Thm_lean_workbook_plus_30754
-- name    : lean_workbook_plus_30754
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/a0d0e27d-c3ff-40ad-86d9-7962a38df749
-- statement:
--   Prove the 'Lemma of Divisibility': Among any $n$ numbers, $a_1,a_2,\ldots,a_n$, one can find some of them, $a_{i_1},a_{i_2},\ldots,a_{i_k}$, whose sum is divisible by $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30754 (n : ℕ) (a : ℕ → ℕ) : ∃ k : ℕ, ∃ I : Finset ℕ, k = I.card ∧ n ∣ ∑ i in I, a i   :=  by sorry
