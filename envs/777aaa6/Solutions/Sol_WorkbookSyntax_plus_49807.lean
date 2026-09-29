-- Prove2me | solution 1 for WorkbookSyntax.plus_49807
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:11:55.748127+00:00
-- url     : https://prove2.me/submissions/649f20aa-cc8f-44b5-8cd1-a7b61639c99a

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem solution (A : Finset ℝ) (hA : ∀ x ∈ A, 0 ≤ x) :
  1 + ∑ x ∈ A, x ≤ ∏ x ∈ A, (1 + x)   := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
    have hAnon : ∀ x ∈ A, 0 ≤ x := fun x hx => hA x (Finset.mem_insert_of_mem hx)
    have ha0 := hA a (Finset.mem_insert_self a A)
    have hs := Finset.sum_nonneg hAnon
    have hi := ih hAnon
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    nlinarith
#print axioms solution
