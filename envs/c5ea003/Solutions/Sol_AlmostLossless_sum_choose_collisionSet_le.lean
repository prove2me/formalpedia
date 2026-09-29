-- Prove2me | solution 1 for AlmostLossless.sum_choose_collisionSet_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T12:12:50.452773+00:00
-- url     : https://prove2.me/submissions/33463893-5971-4c7d-9565-5cf1f5829d34

import Definitions.Def_Bridges_AlmostLosslessListDecoding
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Definitions.Def_Bridges_AlmostLosslessTwiseIndependent
open AlmostLossless in
theorem solution {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ} {H : Fin K → α → Fin M} {T : ℕ}
    (hI : IndepT H T) (S : Finset α) (x : α) :
    (∑ k : Fin K, ((collisionSet H k S x).card.choose T : ℝ)) * (M : ℝ) ^ T
      ≤ (K : ℝ) * (S.card.choose T : ℝ) := by
  have hsum : (∑ k : Fin K, ((collisionSet H k S x).card.choose T : ℝ)) * (M : ℝ) ^ T
      ≤ (K : ℝ) * (S.card.choose T : ℝ) := by
    classical
    have hsub : ∀ k, collisionSet H k S x ⊆ S.erase x := fun k => Finset.filter_subset _ _
    have hcount : ∀ k, (collisionSet H k S x).card.choose T
        = (((S.erase x).powersetCard T).filter (fun t => t ⊆ collisionSet H k S x)).card := by
      intro k
      rw [← Finset.card_powersetCard]
      congr 1
      ext t
      simp only [Finset.mem_powersetCard, Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1.trans (hsub k), h2⟩, h1⟩
      · rintro ⟨⟨_, h2⟩, h1⟩
        exact ⟨h1, h2⟩
    have hiff : ∀ t ∈ (S.erase x).powersetCard T, ∀ k : Fin K,
        (t ⊆ collisionSet H k S x ↔ ∀ y ∈ t, H k y = H k x) := by
      intro t ht k
      have htS : t ⊆ S.erase x := (Finset.mem_powersetCard.mp ht).1
      constructor
      · intro h y hy
        exact (Finset.mem_filter.mp (h hy)).2
      · intro h y hy
        exact Finset.mem_filter.mpr ⟨htS hy, h y hy⟩
    have hswap : (∑ k : Fin K, ((collisionSet H k S x).card.choose T : ℝ))
        = ∑ t ∈ (S.erase x).powersetCard T,
            ((Finset.univ.filter (fun k : Fin K => ∀ y ∈ t, H k y = H k x)).card : ℝ) := by
      simp_rw [hcount, Finset.card_filter]
      push_cast
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun t ht => Finset.sum_congr rfl (fun k _ => ?_))
      simp only [hiff t ht k]
    rw [hswap, Finset.sum_mul]
    calc ∑ t ∈ (S.erase x).powersetCard T,
          ((Finset.univ.filter (fun k : Fin K => ∀ y ∈ t, H k y = H k x)).card : ℝ) * (M : ℝ) ^ T
        ≤ ∑ _t ∈ (S.erase x).powersetCard T, (K : ℝ) := by
          refine Finset.sum_le_sum (fun t ht => ?_)
          have h1 := Finset.mem_powersetCard.mp ht
          exact hI x t h1.2 (fun hx => by simpa using h1.1 hx)
      _ = (K : ℝ) * (((S.erase x).card.choose T : ℕ) : ℝ) := by
          rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, mul_comm]
      _ ≤ (K : ℝ) * (S.card.choose T : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact_mod_cast Nat.choose_le_choose T (Finset.card_erase_le)
  exact hsum
