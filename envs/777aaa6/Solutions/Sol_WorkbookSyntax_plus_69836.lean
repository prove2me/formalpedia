-- Prove2me | solution 1 for WorkbookSyntax.plus_69836
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:15:02.782334+00:00
-- url     : https://prove2.me/submissions/716cbfa9-b03b-44d2-bed2-bb004079e440

/- Source: internlm/Lean-Workbook, Apache-2.0, row lean_workbook_plus_69836.
   The obsolete finite binder is changed from in to ∈; ranges, casts, quantifiers and mathematical expressions are unchanged. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℕ) (a : ℝ) (x : ℕ → ℝ) (h₁ : ∀ i ∈ Finset.range n, 0 ≤ x i) (h₂ : ∀ i ∈ Finset.range n, x i ≤ a) : ∑ i ∈ Finset.range n, x i * (x i - a) ≤ 0   := by
  exact Finset.sum_nonpos (fun i hi => mul_nonpos_of_nonneg_of_nonpos (h₁ i hi) (sub_nonpos.mpr (h₂ i hi)))
#print axioms solution
