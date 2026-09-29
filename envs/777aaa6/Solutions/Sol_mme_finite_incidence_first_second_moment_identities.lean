-- Prove2me | solution 1 for mme_finite_incidence_first_second_moment_identities
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:25:17.7973+00:00
-- url     : https://prove2.me/submissions/b9f5a8d8-2360-4432-87dd-5709d08b696c

import Mathlib

open BigOperators

set_option autoImplicit false

/-- Exact double-counting identities for the first and second moments of a
finite incidence degree. -/
theorem solution
    {Ω α : Type} [DecidableEq Ω] [DecidableEq α]
    (U : Finset Ω) (A : Finset α) (P : Ω → α → Prop)
    [DecidableRel P] :
    (∑ ω ∈ U, (A.filter (fun a => P ω a)).card) =
        ∑ a ∈ A, (U.filter (fun ω => P ω a)).card ∧
    (∑ ω ∈ U, (A.filter (fun a => P ω a)).card ^ 2) =
        ∑ p ∈ A.product A,
          (U.filter (fun ω => P ω p.1 ∧ P ω p.2)).card := by
  classical
  constructor
  · simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  · have hsquare (ω : Ω) :
        (A.filter (fun a => P ω a)).card ^ 2 =
          ((A.product A).filter (fun p => P ω p.1 ∧ P ω p.2)).card := by
      rw [pow_two, ← Finset.card_product]
      congr 1
      ext p
      simp only [Finset.mem_product, Finset.mem_filter]
      aesop
    simp_rw [hsquare]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
