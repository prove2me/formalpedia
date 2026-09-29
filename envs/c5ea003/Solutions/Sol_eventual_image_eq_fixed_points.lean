-- Prove2me | solution 1 for eventual_image_eq_fixed_points
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:09:29.347121+00:00
-- url     : https://prove2.me/submissions/decaf254-46e3-4e8b-8ec7-a0b3be74c89e

-- Sol generated from Bridges/GardenOfEden.lean
import Mathlib
import Definitions.Def_Bridges_GardenOfEden
import Theorems.Thm_finite_garden_of_eden_descent
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
    (hmono : Monotone F)
    (hdesc : ∀ x : P, F x ≤ x) :
    Set.range (F^[Fintype.card P]) = {x | F x = x} := by
  have h_stabilize : ∀ x : P, ∃ n ≤ Fintype.card P,
      F^[n] x = F^[n + 1] x ∧ ∀ k ≥ n, F^[k] x = F^[n] x := by
    intro x
    obtain ⟨n, hn⟩ := finite_garden_of_eden_descent F hmono hdesc x
    use n
    refine ⟨hn.1, hn.2, fun k hk => ?_⟩
    induction hk <;> simp_all +singlePass [Function.iterate_succ_apply']
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨n, hn₁, hn₂, hn₃⟩ := h_stabilize y
    simp +decide [← Function.iterate_succ_apply', hn₃ _ hn₁] at hn₂ ⊢
    exact hn₂.symm
  · intro hx
    exact ⟨x, Function.iterate_fixed hx _⟩
