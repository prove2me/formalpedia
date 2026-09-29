-- Prove2me | solution 1 for mme_finset_common_witness_of_uniform_many
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T10:56:44.012158+00:00
-- url     : https://prove2.me/submissions/19c9b4bd-e443-404d-9172-f3145eee741b

import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (E : Finset α) (U : Finset β) (W : α → Finset β) (B : ℕ)
    (hU : ∀ a ∈ E, W a ⊆ U)
    (hB : ∀ a ∈ E, B ≤ (W a).card)
    (hUne : U.Nonempty) :
    ∃ b ∈ U,
      E.card * B ≤ U.card * (E.filter fun a ↦ b ∈ W a).card := by
  let fiber : β → ℕ := fun b ↦ (E.filter fun a ↦ b ∈ W a).card
  have hincidence :
      ∑ a ∈ E, (W a).card = ∑ b ∈ U, fiber b := by
    calc
      ∑ a ∈ E, (W a).card =
          ∑ a ∈ E, ∑ b ∈ U, if b ∈ W a then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        have hfilter : U.filter (fun b ↦ b ∈ W a) = W a := by
          ext b
          simp only [Finset.mem_filter]
          constructor
          · exact fun hb ↦ hb.2
          · intro hb
            exact ⟨hU a ha hb, hb⟩
        rw [← hfilter, Finset.card_eq_sum_ones, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro b hb
        simp [hb]
      _ = ∑ b ∈ U, ∑ a ∈ E, if b ∈ W a then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ b ∈ U, fiber b := by
        apply Finset.sum_congr rfl
        intro b hb
        simp only [fiber, Finset.card_eq_sum_ones, Finset.sum_filter]
  have himage : (U.image fiber).Nonempty := hUne.image fiber
  let M : ℕ := (U.image fiber).max' himage
  obtain ⟨b, hbU, hbM⟩ := Finset.mem_image.mp
    ((U.image fiber).max'_mem himage)
  refine ⟨b, hbU, ?_⟩
  have hlower : E.card * B ≤ ∑ a ∈ E, (W a).card := by
    simpa [mul_comm] using
      (E.card_nsmul_le_sum (fun a ↦ (W a).card) B hB)
  have hupper : ∑ b ∈ U, fiber b ≤ U.card * M := by
    simpa [mul_comm] using U.sum_le_card_nsmul fiber M (fun b hb ↦ by
      exact (U.image fiber).le_max' (fiber b) (Finset.mem_image.mpr ⟨b, hb, rfl⟩))
  calc
    E.card * B ≤ ∑ a ∈ E, (W a).card := hlower
    _ = ∑ b ∈ U, fiber b := hincidence
    _ ≤ U.card * M := hupper
    _ = U.card * (E.filter fun a ↦ b ∈ W a).card := by
      change U.card * M = U.card * fiber b
      congr 1
      unfold M
      exact hbM.symm
