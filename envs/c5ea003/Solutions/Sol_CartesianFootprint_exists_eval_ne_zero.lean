-- Prove2me | solution 1 for CartesianFootprint.exists_eval_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T01:27:33.02914+00:00
-- url     : https://prove2.me/submissions/d865d10b-4b8c-46de-b953-aefa849df7a8

import Mathlib
import Definitions.Def_Bridges_CartesianFootprintBound
open MvPolynomial Polynomial Finset BigOperators Classical CartesianFootprint in
theorem solution {n : ℕ} {F : Type*} [Field F]
    (S : Fin n → Finset F)
    (hS : ∀ i, (S i).Nonempty)
    (f : MvPolynomial (Fin n) F)
    (hf : f ≠ 0)
    (hred : IsReducedOnGrid S f) :
    ∃ x ∈ grid (F := F) S, MvPolynomial.eval x f ≠ 0 := by
  -- otherwise the Combinatorial Nullstellensatz forces `f = 0`
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  apply hf
  refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset f S (fun i => ?_) (fun x hx => ?_)
  · -- each variable's degree is below the grid side length
    rw [degreeOf_lt_iff (card_pos.2 (hS i))]
    exact fun m hm => hred i m hm
  · exact hall x (Fintype.mem_piFinset.2 hx)
