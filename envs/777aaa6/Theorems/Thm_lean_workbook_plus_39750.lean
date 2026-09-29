-- Prove2me | Theorems.Thm_lean_workbook_plus_39750
-- name    : lean_workbook_plus_39750
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/be6007e8-f25d-42e6-a42f-d891a6578c79
-- statement:
--   Assume that the number of 1's in column $i$ is $a_i$. Then: $S_i=a_i(m-a_i)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39750 (m : ℕ) (a : ℕ → ℕ) (S : ℕ → ℕ) (h₁ : ∀ i, S i = a i * (m - a i)) : ∑ i in Finset.range m, S i = ∑ i in Finset.range m, a i * (m - a i)   :=  by sorry
