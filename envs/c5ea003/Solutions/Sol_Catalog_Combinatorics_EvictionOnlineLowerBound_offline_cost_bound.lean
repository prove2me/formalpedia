-- Prove2me | solution 1 for Catalog.Combinatorics.EvictionOnlineLowerBound.offline_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T04:24:46.275987+00:00
-- url     : https://prove2.me/submissions/025dc710-f47a-44ba-a652-ba073eac16ee

import Mathlib
import Definitions.Def_Combinatorics_EvictionOnlineLowerBound

open Catalog.Combinatorics.EvictionOnlineLowerBound Finset in
theorem solution {α : Type*} [DecidableEq α] [Fintype α] {B : ℕ} (hB : 1 ≤ B)
    (hcard : Fintype.card α = B + 1) :
    ∀ (σ : List α) (C : Finset α), C.card = B → ∃ k, Serves C σ k ∧ k * B < σ.length + B := by
  -- a cache of size `B` misses exactly one of the `B + 1` items
  have huniq : ∀ C : Finset α, C.card = B → ∀ x y, x ∉ C → y ∉ C → x = y := by
    intro C hC x y hx hy
    have h1 : Cᶜ.card = 1 := by
      rw [card_compl, hC, hcard]
      omega
    obtain ⟨z, hz⟩ := card_eq_one.1 h1
    have hx' : x ∈ Cᶜ := mem_compl.2 hx
    have hy' : y ∈ Cᶜ := mem_compl.2 hy
    rw [hz, mem_singleton] at hx' hy'
    rw [hx', hy']
  -- Belady: evict the cached item whose next request lies furthest ahead; then the missing
  -- item is requested for the first time only after `B - 1` other requests
  have key : ∀ (σ : List α) (C : Finset α), C.card = B →
      ∃ k, Serves C σ k ∧ ∀ x ∉ C, k * B + σ.idxOf x ≤ σ.length + (B - 1) := by
    intro σ
    induction σ with
    | nil =>
      intro C _
      refine ⟨0, Serves.nil C, fun x _ => ?_⟩
      simp
    | cons r rest ih =>
      intro C hC
      by_cases hr : r ∈ C
      · obtain ⟨k, hk, hbound⟩ := ih C hC
        refine ⟨k, Serves.hit hr hk, fun x hx => ?_⟩
        have hne : r ≠ x := fun h => hx (h ▸ hr)
        rw [List.idxOf_cons_ne rest hne, List.length_cons]
        have := hbound x hx
        omega
      · have hCne : C.Nonempty := by
          rw [← card_pos, hC]
          omega
        obtain ⟨e, he, hemax⟩ := exists_max_image C (fun y => rest.idxOf y) hCne
        have her : e ≠ r := fun h => hr (h ▸ he)
        have hC'card : (insert r (C.erase e)).card = B := by
          rw [card_insert_of_notMem (fun h => hr (mem_of_mem_erase h)), card_erase_of_mem he, hC]
          omega
        have heC' : e ∉ insert r (C.erase e) := by
          simp only [mem_insert, mem_erase, ne_eq, not_true_eq_false, false_and, or_false]
          exact her
        obtain ⟨k', hk', hbound'⟩ := ih (insert r (C.erase e)) hC'card
        refine ⟨k' + 1, Serves.miss hr he hk', fun x hx => ?_⟩
        have hxr : x = r := huniq C hC x r hx hr
        rw [hxr, List.idxOf_cons_self, List.length_cons]
        have hb := hbound' e heC'
        have hk'B : k' * B ≤ rest.length := by
          rcases Nat.eq_zero_or_pos k' with h0 | hpos
          · rw [h0, zero_mul]
            exact Nat.zero_le _
          · have hBk : B ≤ k' * B := Nat.le_mul_of_pos_left B hpos
            have hlt : rest.idxOf e < rest.length := by omega
            have hmem : e ∈ rest := List.idxOf_lt_length_iff.1 hlt
            -- the other `B - 1` cached items are all requested before `e`
            have hidx : B - 1 ≤ rest.idxOf e := by
              have hinj := card_le_card_of_injOn (fun y => rest.idxOf y) (s := C.erase e)
                (t := range (rest.idxOf e)) ?_ ?_
              · rw [card_erase_of_mem he, hC, card_range] at hinj
                exact hinj
              · intro y hy
                have hy' := mem_erase.1 (mem_coe.1 hy)
                rw [mem_coe, mem_range]
                have h1 := hemax y hy'.2
                have h2 : rest.idxOf y ≠ rest.idxOf e :=
                  fun h => hy'.1 ((List.idxOf_inj hmem).1 h.symm).symm
                simp only at h1 ⊢
                omega
              · intro y hy z hz hyz
                have hy' := mem_erase.1 (mem_coe.1 hy)
                have h1 := hemax y hy'.2
                simp only at h1 hyz
                have hmy : y ∈ rest := List.idxOf_lt_length_iff.1 (by omega)
                exact (List.idxOf_inj hmy).1 hyz
            omega
        rw [add_mul, one_mul]
        omega
  intro σ C hC
  obtain ⟨k, hk, hbound⟩ := key σ C hC
  have hmiss : ∃ x, x ∉ C := by
    by_contra h
    simp only [not_exists, not_not] at h
    have h2 : C = univ := eq_univ_of_forall h
    have h3 := congrArg card h2
    rw [card_univ, hcard, hC] at h3
    omega
  obtain ⟨x, hx⟩ := hmiss
  refine ⟨k, hk, ?_⟩
  have := hbound x hx
  omega
