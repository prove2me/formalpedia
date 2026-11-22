-- Prove2me | solution 1 for BookSixth.sum_func_prod_eq_prod_sum
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T20:18:59.327911+00:00
-- url     : https://prove2.me/submissions/1ad7ef29-5e19-4faf-bb7f-06702cd00a19

import Mathlib
import Definitions.Def_BookSixthRandomGraph

set_option autoImplicit false

open Finset

theorem solution (A : Type) [DecidableEq A] [Fintype A]
    (F : A -> Bool -> Real) :
    Finset.sum Finset.univ (fun b : A -> Bool => Finset.prod Finset.univ (fun e => F e (b e)))
    = Finset.prod Finset.univ (fun e => (F e true + F e false)) := by
  classical
  have hpi : Fintype.piFinset (fun _ : A => (univ : Finset Bool)) = (univ : Finset (A → Bool)) := by
    ext x
    simp [Fintype.mem_piFinset]
  have h := prod_univ_sum (κ := fun _ : A => Bool) (fun _ => univ) (fun e b => F e b)
  have hsum : ∀ e, ∑ b : Bool, F e b = F e true + F e false := by
    intro e
    simp [Fintype.sum_bool]
  simp_rw [hsum] at h
  rw [hpi] at h
  exact h.symm
