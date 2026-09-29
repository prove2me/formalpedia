-- Prove2me | solution 1 for mme_ZMod_two_linear_hash_finset_fiber_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T04:27:10.897836+00:00
-- url     : https://prove2.me/submissions/4eb0b530-80c5-4427-92c9-979c373f7cff

import Mathlib
import Theorems.Thm_mme_ZMod_two_linear_hash_fiber_card

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p n : ℕ} [NeZero p]
    (c d : Fin (n + 2) → ZMod p)
    (j k : Fin (n + 2))
    (hdet : IsUnit (c j * d k - c k * d j))
    (S : Finset (ZMod p)) (t : ZMod p) :
    ((Finset.univ.filter (fun w : Fin (n + 2) → ZMod p ↦
      (∑ i, c i * w i) ∈ S ∧ (∑ i, d i * w i) = t)).card) ≤
        S.card * p ^ n := by
  classical
  let F : ZMod p → Finset (Fin (n + 2) → ZMod p) := fun s ↦
    Finset.univ.filter (fun w ↦
      (∑ i, c i * w i) = s ∧ (∑ i, d i * w i) = t)
  have hsub :
      Finset.univ.filter (fun w : Fin (n + 2) → ZMod p ↦
          (∑ i, c i * w i) ∈ S ∧ (∑ i, d i * w i) = t) ⊆
        S.biUnion F := by
    intro w hw
    have hw' := Finset.mem_filter.mp hw
    refine Finset.mem_biUnion.mpr
      ⟨∑ i, c i * w i, hw'.2.1, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, rfl, hw'.2.2⟩
  calc
    (Finset.univ.filter (fun w : Fin (n + 2) → ZMod p ↦
      (∑ i, c i * w i) ∈ S ∧ (∑ i, d i * w i) = t)).card
        ≤ (S.biUnion F).card := Finset.card_le_card hsub
    _ ≤ ∑ s ∈ S, (F s).card := Finset.card_biUnion_le
    _ = ∑ _s ∈ S, p ^ n := by
      apply Finset.sum_congr rfl
      intro s _hs
      exact mme_ZMod_two_linear_hash_fiber_card c d j k hdet s t
    _ = S.card * p ^ n := by simp
