-- Prove2me | solution 1 for WorkbookSyntax.plus_36732
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:07:05.412671+00:00
-- url     : https://prove2.me/submissions/e6b04f11-2993-4acf-b957-b388ec2c71a7

/- Source: internlm/Lean-Workbook, Apache-2.0, row lean_workbook_plus_36732.
   Only finite binder notation and required imports/namespaces are repaired. -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution  (n : ℕ)
  (h₀ : ∑ k ∈ Finset.Icc 0 6, (n + k) = 3 * (n + 6) + 3) :
  n = 0   := by
  have hs : (Finset.Icc 0 6 : Finset ℕ) = Finset.range 7 := by decide
  rw [hs] at h₀
  norm_num [Finset.sum_range_succ] at h₀
  omega
#print axioms solution
