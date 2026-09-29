-- Prove2me | solution 1 for singleton_bound_rate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T02:12:52.977983+00:00
-- url     : https://prove2.me/submissions/d82f6378-9b12-4515-84fd-50eadd46785b

import Mathlib
import Definitions.Def_Bridges_NeuralCoding_TorsionChannelCodes
open Finset in
theorem solution {len : ℕ} {α : Type*} [DecidableEq α] [Fintype α]
    (C : Finset (Fin len → α)) (d : ℕ)
    (hd : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂) :
    C.card ≤ Fintype.card α ^ (len - (d - 1)) := by
  classical
  set k := len - (d - 1) with hk
  have hkl : k ≤ len := Nat.sub_le _ _
  -- project onto the first `k` coordinates
  let π : (Fin len → α) → (Fin k → α) := fun c j => c ⟨j.1, lt_of_lt_of_le j.2 hkl⟩
  -- the last `len - k` coordinates
  have hmap : (univ.filter (fun i : Fin len => k ≤ i.1)).map Fin.valEmbedding = Ico k len := by
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨hi, i.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
  have hcardtail : (univ.filter (fun i : Fin len => k ≤ i.1)).card = len - k := by
    rw [← card_map, hmap, Nat.card_Ico]
  -- two codewords agreeing on the first `k` coordinates are at distance `≤ len - k < d`
  have hinj : Set.InjOn π C := by
    intro c₁ h₁ c₂ h₂ heq
    by_contra hne
    have hsub : (univ.filter fun i : Fin len => c₁ i ≠ c₂ i)
        ⊆ univ.filter (fun i : Fin len => k ≤ i.1) := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      by_contra hlt
      push_neg at hlt
      apply hi
      have := congrFun heq ⟨i.1, hlt⟩
      simpa [π] using this
    have hdist : hammingDist c₁ c₂ ≤ len - k := by
      rw [← hcardtail]
      exact card_le_card hsub
    have hdd := hd c₁ h₁ c₂ h₂ hne
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · have hz : hammingDist c₁ c₂ = 0 := by omega
      exact hne (hammingDist_eq_zero.mp hz)
    · omega
  -- so `C` injects into the `|α|^k` words of length `k`
  calc C.card ≤ (univ : Finset (Fin k → α)).card :=
        card_le_card_of_injOn π (fun _ _ => mem_univ _) hinj
    _ = Fintype.card α ^ k := by rw [card_univ, Fintype.card_fun, Fintype.card_fin]
