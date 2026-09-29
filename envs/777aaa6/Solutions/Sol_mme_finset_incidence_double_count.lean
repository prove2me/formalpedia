-- Prove2me | solution 1 for mme_finset_incidence_double_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:15:26.861867+00:00
-- url     : https://prove2.me/submissions/80e8c9e1-133f-4929-841b-46ad3cabaf24

import Mathlib

open BigOperators

set_option autoImplicit false

/-- Double-count a finite incidence relation by its two projections. -/
theorem solution
    {Ω A : Type} [DecidableEq Ω] [DecidableEq A]
    (W : Finset Ω) (U : Finset A) (P : Ω → A → Prop)
    [DecidableRel P] :
    (∑ ω ∈ W, (U.filter (P ω)).card) =
      ∑ a ∈ U, (W.filter (fun ω => P ω a)).card := by
  simp_rw [Finset.card_filter]
  exact Finset.sum_comm
