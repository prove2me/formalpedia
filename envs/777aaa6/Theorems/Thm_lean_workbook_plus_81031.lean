-- Prove2me | Theorems.Thm_lean_workbook_plus_81031
-- name    : lean_workbook_plus_81031
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/bf89cdfa-cc1c-4905-80ec-12888cb28bf1
-- statement:
--   Is it possible to show that $\forall k\in\{0,1,2,\cdots,p-1\},\exists i,j\in\{0,1,2,\cdots,p-1\}$ s.t. $i!j!\equiv k(\text{mod}p)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81031 : ∀ p : ℕ, p.Prime → ∀ k : ℕ, k < p → ∃ i j : ℕ, i < p ∧ j < p ∧ (i! * j!) % p = k   :=  by sorry
