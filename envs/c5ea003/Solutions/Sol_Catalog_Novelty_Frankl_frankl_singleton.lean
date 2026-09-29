-- Prove2me | solution 1 for Catalog.Novelty.Frankl.frankl_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T21:13:03.260509+00:00
-- url     : https://prove2.me/submissions/e5f0c283-f968-4e77-9818-d2c4699acb05

import Mathlib
import Definitions.Def_Novelty_FranklUnionClosed
open Catalog.Novelty.Frankl in
theorem solution {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (hF : IsUnionClosed F)
    (a : α) (ha : ({a} : Finset α) ∈ F) : Abundant F a := by
  unfold Abundant containing
  have hsplit := Finset.card_filter_add_card_filter_not (s := F) (fun A => a ∈ A)
  -- `A ↦ A ∪ {a}` injects the members avoiding `a` into those containing it
  have hle : (F.filter fun A => a ∉ A).card ≤ (F.filter fun A => a ∈ A).card := by
    apply Finset.card_le_card_of_injOn (fun A => insert a A)
    · intro A hA
      simp only [Finset.mem_coe, Finset.mem_filter] at hA ⊢
      refine ⟨?_, Finset.mem_insert_self a A⟩
      have h := hF A hA.1 {a} ha
      rwa [Finset.union_comm, ← Finset.insert_eq] at h
    · intro A hA B hB hAB
      simp only [Finset.mem_coe, Finset.mem_filter] at hA hB
      have h := congrArg (fun S => S.erase a) hAB
      simpa [Finset.erase_insert hA.2, Finset.erase_insert hB.2] using h
  omega
