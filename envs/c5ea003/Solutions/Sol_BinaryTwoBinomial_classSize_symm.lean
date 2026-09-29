-- Prove2me | solution 1 for BinaryTwoBinomial.classSize_symm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T12:44:51.946524+00:00
-- url     : https://prove2.me/submissions/bbd26fed-b5f6-43d3-ba46-fefa73979c41

import Mathlib
import Definitions.Def_Probability_BinaryTwoBinomial
open BinaryTwoBinomial Finset in
theorem solution (n k i : ℕ) (hi : i ≤ k * (n - k)) :
    classSize n k i = classSize n k (k * (n - k) - i) := by
  classical
  let R : Fin n ↪ Fin n := ⟨Fin.rev, Fin.rev_injective⟩
  have hmemR : ∀ (S : Finset (Fin n)) (b : Fin n), b ∈ S.map R ↔ Fin.rev b ∈ S := by
    intro S b
    rw [mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa [R] using ha
    · intro h
      exact ⟨Fin.rev b, h, Fin.rev_rev b⟩
  -- inversions + co-inversions = k(n − k): together they are the pairs (one, zero)
  have hsum : ∀ S : Finset (Fin n), S.card = k → invF S + coinvF S = k * (n - k) := by
    intro S hS
    unfold invF coinvF
    have hswap : (univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ p.1 ∉ S ∧ p.2 ∈ S)).card
        = (univ.filter (fun p : Fin n × Fin n => p.2 < p.1 ∧ p.1 ∈ S ∧ p.2 ∉ S)).card := by
      apply card_bij (fun p _ => p.swap)
      · intro p hp
        simp only [mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap] at hp ⊢
        tauto
      · intro p _ q _ h
        exact Prod.swap_injective h
      · intro q hq
        refine ⟨q.swap, ?_, Prod.swap_swap q⟩
        simp only [mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap] at hq ⊢
        tauto
    rw [hswap, ← card_union_of_disjoint]
    · have hU : (univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S))
          ∪ (univ.filter (fun p : Fin n × Fin n => p.2 < p.1 ∧ p.1 ∈ S ∧ p.2 ∉ S)) = S ×ˢ Sᶜ := by
        ext ⟨a, b⟩
        simp only [mem_union, mem_filter, mem_univ, true_and, mem_product, mem_compl]
        constructor
        · rintro (⟨-, h1, h2⟩ | ⟨-, h1, h2⟩) <;> exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          have hab : a ≠ b := fun h => h2 (h ▸ h1)
          rcases lt_or_gt_of_ne hab with h | h
          · exact Or.inl ⟨h, h1, h2⟩
          · exact Or.inr ⟨h, h1, h2⟩
      rw [hU, card_product, card_compl, Fintype.card_fin, hS]
    · rw [disjoint_left]
      intro p hp hq
      simp only [mem_filter] at hp hq
      exact absurd (hp.2.1.trans hq.2.1) (lt_irrefl _)
  -- reversing the word swaps inversions and co-inversions
  have hrev : ∀ S : Finset (Fin n), invF (S.map R) = coinvF S := by
    intro S
    unfold invF coinvF
    apply card_bij (fun p _ => (Fin.rev p.2, Fin.rev p.1))
    · intro p hp
      simp only [mem_filter, mem_univ, true_and, hmemR] at hp ⊢
      exact ⟨Fin.rev_lt_rev.mpr hp.1, hp.2.2, hp.2.1⟩
    · intro p _ q _ h
      simp only [Prod.mk.injEq, Fin.rev_inj] at h
      exact Prod.ext h.2 h.1
    · intro q hq
      refine ⟨(Fin.rev q.2, Fin.rev q.1), ?_, by simp⟩
      simp only [mem_filter, mem_univ, true_and, hmemR, Fin.rev_rev] at hq ⊢
      exact ⟨Fin.rev_lt_rev.mpr hq.1, hq.2.2, hq.2.1⟩
  have hRR : ∀ S : Finset (Fin n), (S.map R).map R = S := by
    intro S
    ext b
    rw [hmemR, hmemR, Fin.rev_rev]
  unfold classSize words
  apply card_bij (fun S _ => S.map R)
  · intro S hS
    simp only [mem_filter, mem_powersetCard] at hS ⊢
    refine ⟨⟨subset_univ _, by rw [card_map]; exact hS.1.2⟩, ?_⟩
    rw [hrev]
    have := hsum S hS.1.2
    omega
  · intro S _ T _ h
    exact map_injective R h
  · intro T hT
    simp only [mem_filter, mem_powersetCard] at hT
    refine ⟨T.map R, ?_, hRR T⟩
    simp only [mem_filter, mem_powersetCard]
    refine ⟨⟨subset_univ _, by rw [card_map]; exact hT.1.2⟩, ?_⟩
    rw [hrev]
    have := hsum T hT.1.2
    omega
