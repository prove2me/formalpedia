-- Prove2me | solution 1 for Catalog.Novelty.Frankl.franklProperty_of_singleton_mem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T16:10:05.838067+00:00
-- url     : https://prove2.me/submissions/86c99a88-64a0-4185-ae3f-ebfe5a9942ab

import Mathlib
import Definitions.Def_Combinatorics_FranklUnionClosed
open Catalog.Novelty.Frankl Finset in
theorem solution {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hF : IsUnionClosed F) (a : α) (ha : ({a} : Finset α) ∈ F) :
    FranklProperty F := by
  refine ⟨a, ⟨{a}, ha, mem_singleton_self a⟩, ?_⟩
  unfold Abundant containing
  -- `S ↦ S ∪ {a}` injects the members avoiding `a` into the members containing `a`
  have hinj : (F.filter (fun A => a ∉ A)).card ≤ (F.filter (fun A => a ∈ A)).card := by
    refine card_le_card_of_injOn (fun S => S ∪ {a}) (fun S hS => ?_) (fun S hS T hT hST => ?_)
    · rw [mem_coe, mem_filter] at hS
      rw [mem_coe, mem_filter]
      exact ⟨hF S hS.1 {a} ha, mem_union_right _ (mem_singleton_self a)⟩
    · rw [mem_coe, mem_filter] at hS hT
      have h1 := congrArg (fun U => U.erase a) hST
      simp only [union_comm _ {a}, ← insert_eq, erase_insert hS.2, erase_insert hT.2] at h1
      exact h1
  have hsplit := card_filter_add_card_filter_not (s := F) (fun A => a ∈ A)
  omega
