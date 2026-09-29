-- Prove2me | solution 1 for WorkbookSyntax.plus_39501
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:07:08.104566+00:00
-- url     : https://prove2.me/submissions/1d076bf4-fa71-44e0-8513-4bc57efde6bc

/- Source: internlm/Lean-Workbook, Apache-2.0, row lean_workbook_plus_39501.
   Only finite binder notation and required imports/namespaces are repaired. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
theorem solution : ∀ n : ℕ, n ∈ ({1, 2, 3, 4} : Finset ℕ) → ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k ^ 2 < 5 / 3   := by
  intro n hn
  have hn' : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by simpa using hn
  change (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k ^ 2) < (5 : ℝ) / 3
  rcases hn' with rfl | rfl | rfl | rfl <;>
    norm_num [show (Finset.Icc 1 1 : Finset ℕ) = {1} by decide,
      show (Finset.Icc 1 2 : Finset ℕ) = {1, 2} by decide,
      show (Finset.Icc 1 3 : Finset ℕ) = {1, 2, 3} by decide,
      show (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} by decide]
#print axioms solution
