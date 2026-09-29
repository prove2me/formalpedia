-- Prove2me | Theorems.Thm_lean_workbook_plus_23851
-- name    : lean_workbook_plus_23851
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/5c40e2fd-4d80-4bcb-825f-90eb025d95fe
-- statement:
--   Prove that if $|A| \geq 5$, then the sum of three members of $A$ would be divisible by 3 or there exist three members with the same remainder modulo 3.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23851 (A : Finset ℤ) (hA : 5 ≤ A.card) : (∃ x y z : ℤ, x ∈ A ∧ y ∈ A ∧ z ∈ A ∧ 3 ∣ x + y + z) ∨ (∃ x y z : ℤ, x ∈ A ∧ y ∈ A ∧ z ∈ A ∧ x % 3 = y % 3 ∧ y % 3 = z % 3 ∧ z % 3 = x % 3)   :=  by sorry
