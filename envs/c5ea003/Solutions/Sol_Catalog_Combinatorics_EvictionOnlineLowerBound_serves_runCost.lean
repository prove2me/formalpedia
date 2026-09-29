-- Prove2me | solution 1 for Catalog.Combinatorics.EvictionOnlineLowerBound.serves_runCost
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T23:57:49.401899+00:00
-- url     : https://prove2.me/submissions/122309ed-9cae-4284-b172-c49e1d8f079a

import Mathlib
import Definitions.Def_Combinatorics_EvictionOnlineLowerBound
open Finset Catalog.Combinatorics.EvictionOnlineLowerBound in
theorem solution {α : Type*} [DecidableEq α] {B : ℕ} (A : Finset α → α → α)
    (hA : ∀ C : Finset α, C.card = B → ∀ r, A C r ∈ C) :
    ∀ (σ : List α) (C : Finset α), C.card = B → Serves C σ (runCost A σ C) := by
  intro σ
  induction σ with
  | nil =>
    intro C _
    exact Serves.nil C
  | cons r rest ih =>
    intro C hC
    by_cases hr : r ∈ C
    · -- a hit: the cache is unchanged
      have e : runCost A (r :: rest) C = runCost A rest C := by
        simp [runCost, hr]
      rw [e]
      exact Serves.hit hr (ih C hC)
    · -- a miss: evict `A C r`, which lies in the cache, and keep `B` items
      have he := hA C hC r
      have hC' : (insert r (C.erase (A C r))).card = B := by
        have hB : 1 ≤ C.card := card_pos.2 ⟨_, he⟩
        rw [card_insert_of_notMem (fun h => hr (mem_of_mem_erase h)), card_erase_of_mem he]
        omega
      have e : runCost A (r :: rest) C = runCost A rest (insert r (C.erase (A C r))) + 1 := by
        simp [runCost, hr]
      rw [e]
      exact Serves.miss hr he (ih _ hC')
