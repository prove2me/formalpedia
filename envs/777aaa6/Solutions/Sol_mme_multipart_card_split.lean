-- Prove2me | solution 1 for mme_multipart_card_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T06:04:46.403738+00:00
-- url     : https://prove2.me/submissions/1479964c-cb2f-4e01-a5a8-f84254e29d00

import Mathlib

open BigOperators
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u


namespace MME.MultiSplit

/-- Counting a property of blocks splits over the parts. -/
theorem card_split {B : Type u} [Fintype B] {p : ℕ} (part : B → Fin p) (P : B → Prop) :
    Fintype.card {b : B // P b} = ∑ j, Fintype.card {b : B // part b = j ∧ P b} := by
  classical
  rw [Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := part) (s := Finset.univ.filter P) (t := Finset.univ)
    (fun b _ ↦ Finset.mem_univ (part b))]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  rw [Fintype.card_subtype]
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto


end MME.MultiSplit

theorem solution :
    ∀ {B : Type u} [Fintype B] {p : ℕ} (part : B → Fin p) (P : B → Prop),
      Fintype.card {b : B // P b} = ∑ j, Fintype.card {b : B // part b = j ∧ P b} :=
  fun {B} _ {p} part P ↦ MME.MultiSplit.card_split part P
