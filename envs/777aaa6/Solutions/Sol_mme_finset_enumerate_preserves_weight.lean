-- Prove2me | solution 1 for mme_finset_enumerate_preserves_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T22:52:09.619895+00:00
-- url     : https://prove2.me/submissions/394ed454-fd2d-4a96-9b23-6d3320bb6cc5

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (I : Finset α) (weight : α → M) :
    ∃ edge : Fin I.card → α,
      Function.Injective edge ∧
      (∀ r, edge r ∈ I) ∧
      (∀ a, a ∈ I → ∃ r, edge r = a) ∧
      (∑ r, weight (edge r)) = ∑ a ∈ I, weight a := by
  classical
  let enum : Fin I.card ≃ ↥I := I.equivFin.symm
  let edge : Fin I.card → α := fun r ↦ (enum r).1
  refine ⟨edge, ?_, ?_, ?_, ?_⟩
  · intro r s hrs
    exact enum.injective (Subtype.ext hrs)
  · intro r
    exact (enum r).2
  · intro a ha
    let aI : ↥I := ⟨a, ha⟩
    exact ⟨enum.symm aI, by simp only [edge, Equiv.apply_symm_apply, aI]⟩
  · calc
      (∑ r, weight (edge r)) = ∑ a : ↥I, weight a.1 := by
        exact Equiv.sum_comp enum (fun a : ↥I ↦ weight a.1)
      _ = ∑ a ∈ I.attach, weight a.1 := by
        exact Finset.sum_coe_sort_eq_attach I
          (fun a : ↥I ↦ weight a.1)
      _ = ∑ a ∈ I, weight a := Finset.sum_attach I weight
