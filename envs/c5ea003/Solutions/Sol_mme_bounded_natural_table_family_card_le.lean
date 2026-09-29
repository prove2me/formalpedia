-- Prove2me | solution 1 for mme_bounded_natural_table_family_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:55:27.049754+00:00
-- url     : https://prove2.me/submissions/a42d81b4-b33c-4183-b3d5-f539307318bd

import Mathlib

set_option autoImplicit false

/-- A family of `k`-cell natural tables with every cell at most `N` has at
most `(N+1)^k` members. -/
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
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
