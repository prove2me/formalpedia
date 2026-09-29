-- Prove2me | solution 1 for mme_finset_equal_or_opposite_code_pairs_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:25:17.032076+00:00
-- url     : https://prove2.me/submissions/74f3ab4a-5e0a-42cc-9cc9-5bdf7e23d84c

import Mathlib

set_option autoImplicit false

/-- An injective code has at most two equal-or-opposite partners for each
element of a finite set. -/
theorem solution
    {α R : Type} [DecidableEq α] [DecidableEq R] [AddGroup R]
    (A : Finset α) (c : α → R) (hc : Function.Injective c) :
    (((A.product A).filter (fun p =>
      c p.1 = c p.2 ∨ c p.1 = -c p.2)).card) ≤ 2 * A.card := by
  let EqPairs := (A.product A).filter (fun p => c p.1 = c p.2)
  let NegPairs := (A.product A).filter (fun p => c p.1 = -c p.2)
  have heqCard : EqPairs.card ≤ A.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    · intro p hp q hq hpq
      apply Prod.ext hpq
      apply hc
      have hpRel := (Finset.mem_filter.mp hp).2
      have hqRel := (Finset.mem_filter.mp hq).2
      rw [← hpRel, ← hqRel, hpq]
  have hnegCard : NegPairs.card ≤ A.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    · intro p hp q hq hpq
      apply Prod.ext hpq
      apply hc
      have hpRel := (Finset.mem_filter.mp hp).2
      have hqRel := (Finset.mem_filter.mp hq).2
      rw [← neg_inj]
      rw [← hpRel, ← hqRel, hpq]
  have hsubset :
      (A.product A).filter (fun p => c p.1 = c p.2 ∨ c p.1 = -c p.2) ⊆
        EqPairs ∪ NegPairs := by
    intro p hp
    rcases (Finset.mem_filter.mp hp).2 with hpEq | hpNeg
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hp).1, hpEq⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hp).1, hpNeg⟩)
  calc
    ((A.product A).filter (fun p =>
        c p.1 = c p.2 ∨ c p.1 = -c p.2)).card ≤
        (EqPairs ∪ NegPairs).card := Finset.card_le_card hsubset
    _ ≤ EqPairs.card + NegPairs.card := Finset.card_union_le EqPairs NegPairs
    _ ≤ A.card + A.card := Nat.add_le_add heqCard hnegCard
    _ = 2 * A.card := by omega
