-- Prove2me | solution 1 for AlmostLossless.exists_good_key_indepT
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T14:06:12.203955+00:00
-- url     : https://prove2.me/submissions/c5d2657d-e8d9-44fe-8996-533d2039801a

import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_AlmostLosslessListDecoding
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Definitions.Def_Bridges_AlmostLosslessTwiseIndependent
import Definitions.Def_Bridges_MinEntropy
open AlmostLossless NonArchInfoTheory in
theorem solution {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ} (μ : FinProbDist α)
    {H : Fin K → α → Fin M} {T : ℕ} (hI : IndepT H T) (hK : 0 < K) (S A : Finset α) :
    ∃ k : Fin K, (M : ℝ) ^ T *
        setMass μ (A.filter (fun x => T ≤ (collisionSet H k S x).card))
      ≤ (S.card.choose T : ℝ) * setMass μ A := by
  have hmain : (M : ℝ) ^ T *
        ∑ k : Fin K, setMass μ (A.filter (fun x => T ≤ (collisionSet H k S x).card))
      ≤ (K : ℝ) * (S.card.choose T : ℝ) * setMass μ A := by
    have hbadT : ∀ x : α,
        ((badKeysT H S x T).card : ℝ) * (M : ℝ) ^ T ≤ (K : ℝ) * (S.card.choose T : ℝ) := by
      intro x
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
      have hbad : ((badKeysT H S x T).card : ℝ)
          ≤ ∑ k : Fin K, ((collisionSet H k S x).card.choose T : ℝ) := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum]
        calc ∑ k ∈ badKeysT H S x T, ((1 : ℕ) : ℝ)
            ≤ ∑ k ∈ badKeysT H S x T, ((collisionSet H k S x).card.choose T : ℝ) := by
              refine Finset.sum_le_sum (fun k hk => ?_)
              have hT := (Finset.mem_filter.mp hk).2
              exact_mod_cast Nat.choose_pos hT
          _ ≤ ∑ k : Fin K, ((collisionSet H k S x).card.choose T : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun _ _ _ => Nat.cast_nonneg _)
      calc ((badKeysT H S x T).card : ℝ) * (M : ℝ) ^ T
          ≤ (∑ k : Fin K, ((collisionSet H k S x).card.choose T : ℝ)) * (M : ℝ) ^ T :=
            mul_le_mul_of_nonneg_right hbad (by positivity)
        _ ≤ (K : ℝ) * (S.card.choose T : ℝ) := hsum
    unfold setMass
    have hswap : ∑ k : Fin K, ∑ x ∈ A.filter (fun x => T ≤ (collisionSet H k S x).card), μ.mass x
        = ∑ x ∈ A, μ.mass x * ((badKeysT H S x T).card : ℝ) := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      unfold badKeysT
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      split_ifs <;> simp
    rw [hswap, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum (fun x _ => ?_)
    have hk := hbadT x
    have hμ := μ.mass_nonneg x
    nlinarith [mul_le_mul_of_nonneg_left hk hμ]
  by_contra hall
  push Not at hall
  have hlt : ∑ _k : Fin K, (S.card.choose T : ℝ) * setMass μ A
      < ∑ k : Fin K, (M : ℝ) ^ T * setMass μ (A.filter (fun x => T ≤ (collisionSet H k S x).card)) :=
    Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hK⟩⟩) (fun k _ => hall k)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hlt
  nlinarith
