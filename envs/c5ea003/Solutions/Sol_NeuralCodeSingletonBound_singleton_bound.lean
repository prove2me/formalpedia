-- Prove2me | solution 1 for NeuralCodeSingletonBound.singleton_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T02:17:35.614985+00:00
-- url     : https://prove2.me/submissions/4c83493a-bdef-4ea8-838f-19aac9cb2c72

import Mathlib
import Definitions.Def_Novelty_NeuralCodeSingletonBound
import Definitions.Def_Novelty_NeuralCoding
open NeuralCodeSingletonBound Finset in
theorem solution {N d : ℕ} (hd : 1 ≤ d) (hdN : d ≤ N + 1)
    (C : Finset (NeuralCode N))
    (hmin : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y) :
    C.card ≤ 2 ^ (N + 1 - d) := by
  -- the Singleton bound over the binary alphabet
  have hS : C.card ≤ Fintype.card Bool ^ (N - (d - 1)) := by
    classical
    set k := N - (d - 1) with hk
    have hkl : k ≤ N := Nat.sub_le _ _
    -- project onto the first `k` coordinates
    let π : (Fin N → Bool) → (Fin k → Bool) := fun c j => c ⟨j.1, lt_of_lt_of_le j.2 hkl⟩
    -- the last `N - k` coordinates
    have hmap : (univ.filter (fun i : Fin N => k ≤ i.1)).map Fin.valEmbedding = Ico k N := by
      ext x
      simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨hi, i.2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨x, h2⟩, h1, rfl⟩
    have hcardtail : (univ.filter (fun i : Fin N => k ≤ i.1)).card = N - k := by
      rw [← card_map, hmap, Nat.card_Ico]
    -- two codewords agreeing on the first `k` coordinates are at distance `≤ N - k < d`
    have hinj : Set.InjOn π C := by
      intro c₁ h₁ c₂ h₂ heq
      by_contra hne
      have hsub : (univ.filter fun i : Fin N => c₁ i ≠ c₂ i)
          ⊆ univ.filter (fun i : Fin N => k ≤ i.1) := by
        intro i hi
        simp only [mem_filter, mem_univ, true_and] at hi ⊢
        by_contra hlt
        push_neg at hlt
        apply hi
        have := congrFun heq ⟨i.1, hlt⟩
        simpa [π] using this
      have hdist : hammingDist c₁ c₂ ≤ N - k := by
        rw [← hcardtail]
        exact card_le_card hsub
      have hdd := hmin c₁ h₁ c₂ h₂ hne
      rcases Nat.eq_zero_or_pos d with h0 | hpos
      · have hz : hammingDist c₁ c₂ = 0 := by omega
        exact hne (hammingDist_eq_zero.mp hz)
      · omega
    -- so `C` injects into the `|α|^k` words of Ngth `k`
    calc C.card ≤ (univ : Finset (Fin k → Bool)).card :=
          card_le_card_of_injOn π (fun _ _ => mem_univ _) hinj
      _ = Fintype.card Bool ^ k := by rw [card_univ, Fintype.card_fun, Fintype.card_fin]
  rw [Fintype.card_bool] at hS
  rwa [show N + 1 - d = N - (d - 1) by omega]
