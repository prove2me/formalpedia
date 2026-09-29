-- Prove2me | Theorems.Thm_lean_workbook_plus_18918
-- name    : lean_workbook_plus_18918
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/dbbd77ff-3212-4250-9aee-494118f75946
-- statement:
--   Let $n$ be a positive integer. Let $A = \{1,2 \dots, 2n \}, S \subset A$ with $n+1$ elements. Show there exist two elements of $S$ , one of which divides the other.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18918 (n : ℕ) (hn : 0 < n) (A : Finset ℕ) (hA : A = Finset.Icc 1 (2 * n)) (S : Finset ℕ) (hS : S ⊆ A) (hS' : n + 1 ≤ S.card) : ∃ x ∈ S, ∃ y ∈ S, x ∣ y   :=  by sorry
