-- Prove2me | solution 1 for finite_garden_of_eden_descent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:07:07.465884+00:00
-- url     : https://prove2.me/submissions/8f4d09cd-e6c5-4a3c-a2c0-cf25bfc71bdb

-- Sol generated from Bridges/GardenOfEden.lean
import Mathlib
import Definitions.Def_Bridges_GardenOfEden
/-
# Finite Garden-of-Eden Principle

A formal treatment of the Garden-of-Eden theorem for finite dynamical systems,
establishing that non-surjective dynamics on finite state spaces produce
permanently unreachable ("Garden-of-Eden") configurations, and that monotone
descending maps on finite partial orders stabilize in bounded time.

## Main Results

- `iterate_descends`: Iterates of a descending map form a descending chain.
- `finite_garden_of_eden_descent`: Every orbit of a monotone descending map on a
  finite partial order stabilizes within `Fintype.card P` steps.
- `finite_garden_of_eden_of_not_surjective`: A non-surjective monotone descending map
  has a Garden-of-Eden state outside the eventual image.
- `finite_configuration_garden_of_eden`: On finite configuration spaces, non-surjective
  maps have unreachable configurations.
- `preinjective_of_surjective_on_finite_configurations`: Finite Moore–Myhill shadow —
  surjectivity implies injectivity on finite types.

## Concepts

A **Garden-of-Eden** state is a configuration with no preimage under the dynamics.
The **eventual image** is the range of sufficiently many iterates.
**Descent-stabilization** means every orbit reaches a fixed point in bounded time.
-/


open Function Set










theorem solution    {P : Type*} [Fintype P] [DecidableEq P] [PartialOrder P]
    (F : P → P)
    (_hmono : Monotone F)
    (hdesc : ∀ x : P, F x ≤ x) :
    ∀ x : P, ∃ n ≤ Fintype.card P, F^[n] x = F^[n + 1] x := by
  intro x
  by_contra h_contra
  push_neg at h_contra
  have h_ne : ∀ n ≤ Fintype.card P, F^[n] x ≠ F^[n + 1] x := by finiteness
  have h_card : Finset.card (Finset.image (fun n => F^[n] x)
      (Finset.range (Fintype.card P + 1))) = Fintype.card P + 1 := by
    nontriviality
    have h_strict : ∀ m n : ℕ, m < n → n ≤ Fintype.card P → F^[m] x ≠ F^[n] x := by
      intro m n mn hn hmn
      induction mn <;> simp_all +decide [Function.iterate_succ_apply']
      · exact h_contra m hn.le hmn
      · have h_bound : ∀ k ≥ m + 1, F^[k] x ≤ F^[m + 1] x := by
          intro k hk; induction hk <;> simp_all +decide [Function.iterate_succ_apply']
          grind
        have := h_bound _ (Nat.succ_le_of_lt ‹_›)
        simp_all +decide [Function.iterate_succ_apply']
        grind
    rw [Finset.card_image_of_injOn fun m hm n hn hmn =>
      le_antisymm
        (le_of_not_gt fun hmn' =>
          h_strict _ _ hmn' (Finset.mem_range_succ_iff.mp hm) hmn.symm)
        (le_of_not_gt fun hmn' =>
          h_strict _ _ hmn' (Finset.mem_range_succ_iff.mp hn) hmn),
      Finset.card_range]
  exact h_card.not_lt (lt_of_le_of_lt (Finset.card_le_univ _) (by simp +decide))
