-- Prove2me | solution 1 for mme_bounded_natural_table_family_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T23:35:06.093816+00:00
-- url     : https://prove2.me/submissions/ed2ab258-9eca-4a39-9e47-bcc0965bd37d

import Mathlib

open BigOperators

set_option autoImplicit false

theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : Finset (ι → ℕ)) (N : ℕ)
    (hbound : ∀ a ∈ T, ∀ i, a i ≤ N) :
    T.card ≤ (N + 1) ^ Fintype.card ι := by
  let encode : T → (ι → Fin (N + 1)) := fun a i =>
    ⟨a.1 i, Nat.lt_succ_of_le (hbound a.1 a.2 i)⟩
  have hencode : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun hab i)
  calc
    T.card = Fintype.card T := by simp
    _ ≤ Fintype.card (ι → Fin (N + 1)) :=
      Fintype.card_le_of_injective encode hencode
    _ = (N + 1) ^ Fintype.card ι := by simp
