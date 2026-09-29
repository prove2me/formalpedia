-- Prove2me | Theorems.Thm_lean_workbook_plus_29686
-- name    : lean_workbook_plus_29686
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/96090d3c-4bab-4c05-ae89-0abbb0e9535c
-- statement:
--   Prove that $a_i$ =i for all i given $a_0,a_1,\dots,a_n$ is a sequence of positive integers such that: ( $a_i,a_j$ )=( $i,j$ ) for all i $\neq$ j.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29686 {n : ℕ} (a : ℕ → ℕ) (h₀ : ∀ i, 0 < a i) (h₁ : ∀ i j, i ≠ j → (a i, a j) = (i, j)) : ∀ i, a i = i   :=  by sorry
