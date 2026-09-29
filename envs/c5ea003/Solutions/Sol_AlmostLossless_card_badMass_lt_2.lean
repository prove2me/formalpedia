-- Prove2me | solution 2 for AlmostLossless.card_badMass_lt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T13:44:03.305023+00:00
-- url     : https://prove2.me/submissions/05de93f6-1bf2-4f0b-a3c5-cf702d0e1335

import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Definitions.Def_Bridges_AlmostLosslessSharpSilent
import Definitions.Def_Bridges_MinEntropy
open AlmostLossless NonArchInfoTheory in
theorem solution {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ} (μ : FinProbDist α)
    {H : Fin K → α → Fin M} (hU : Universal2 H) (hK : 0 < K) (S A : Finset α) :
    ((badMassKeys μ H S A).card : ℝ) * 2 < K := by
  have hsum : ∀ (S A : Finset α), (M : ℝ) * ∑ k : Fin K, setMass μ (A.filter (fun x => Collides H k S x))
      ≤ (K : ℝ) * S.card * setMass μ A := by
    intro S A
    unfold setMass
    have hswap : ∑ k : Fin K, ∑ x ∈ A.filter (fun x => Collides H k S x), μ.mass x
        = ∑ x ∈ A, μ.mass x * ((Finset.univ.filter (fun k => Collides H k S x)).card : ℝ) := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      split_ifs <;> simp
    have hkeys : ∀ x, ((Finset.univ.filter (fun k => Collides H k S x)).card : ℝ) * M
        ≤ S.card * K := by
      intro x
      have hsub : Finset.univ.filter (fun k => Collides H k S x)
          ⊆ (S.erase x).biUnion (fun y => Finset.univ.filter (fun k => H k y = H k x)) := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Collides, collisionSet,
          Finset.Nonempty] at hk
        obtain ⟨y, hy⟩ := hk
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨y, hy.1, hy.2⟩
      have h1 : ((Finset.univ.filter (fun k => Collides H k S x)).card : ℝ)
          ≤ ∑ y ∈ S.erase x, ((Finset.univ.filter (fun k => H k y = H k x)).card : ℝ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      have h2 : ∀ y ∈ S.erase x, ((Finset.univ.filter (fun k => H k y = H k x)).card : ℝ) * M ≤ K :=
        fun y hy => hU y x (Finset.ne_of_mem_erase hy)
      have hce : ((S.erase x).card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_erase_le
      calc ((Finset.univ.filter (fun k => Collides H k S x)).card : ℝ) * M
          ≤ (∑ y ∈ S.erase x, ((Finset.univ.filter (fun k => H k y = H k x)).card : ℝ)) * M :=
            mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
        _ = ∑ y ∈ S.erase x, ((Finset.univ.filter (fun k => H k y = H k x)).card : ℝ) * M :=
            Finset.sum_mul _ _ _
        _ ≤ ∑ _y ∈ S.erase x, (K : ℝ) := Finset.sum_le_sum h2
        _ = ((S.erase x).card : ℝ) * K := by simp
        _ ≤ S.card * K := mul_le_mul_of_nonneg_right hce (Nat.cast_nonneg _)
    rw [hswap, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum (fun x _ => ?_)
    have hk := hkeys x
    have hμ := μ.mass_nonneg x
    nlinarith [mul_le_mul_of_nonneg_left hk hμ]
  have hbad : ∀ (S A : Finset α), ((badMassKeys μ H S A).card : ℝ) * 2 < K := by
    intro S A
    have hX0 : 0 ≤ (S.card : ℝ) * setMass μ A :=
      mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun x _ => μ.mass_nonneg x))
    have hf0 : ∀ k : Fin K, 0 ≤ (M : ℝ) * setMass μ (A.filter (fun x => Collides H k S x)) :=
      fun k => mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun x _ => μ.mass_nonneg x))
    have hS' : ∑ k : Fin K, (M : ℝ) * setMass μ (A.filter (fun x => Collides H k S x))
        ≤ (K : ℝ) * ((S.card : ℝ) * setMass μ A) := by
      rw [← Finset.mul_sum]
      have := hsum S A
      linarith
    by_cases hne : (badMassKeys μ H S A).Nonempty
    · have hlt : ∑ _k ∈ badMassKeys μ H S A, 2 * ((S.card : ℝ) * setMass μ A)
          < ∑ k ∈ badMassKeys μ H S A, (M : ℝ) * setMass μ (A.filter (fun x => Collides H k S x)) :=
        Finset.sum_lt_sum_of_nonempty hne (fun k hk => (Finset.mem_filter.mp hk).2)
      have hle : ∑ k ∈ badMassKeys μ H S A, (M : ℝ) * setMass μ (A.filter (fun x => Collides H k S x))
          ≤ ∑ k : Fin K, (M : ℝ) * setMass μ (A.filter (fun x => Collides H k S x)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => hf0 k)
      rw [Finset.sum_const, nsmul_eq_mul] at hlt
      have h3 : ((badMassKeys μ H S A).card : ℝ) * 2 * ((S.card : ℝ) * setMass μ A)
          < (K : ℝ) * ((S.card : ℝ) * setMass μ A) := by
        linarith
      exact lt_of_mul_lt_mul_right h3 hX0
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.card_empty, Nat.cast_zero, zero_mul]
      exact_mod_cast hK
  exact hbad S A
