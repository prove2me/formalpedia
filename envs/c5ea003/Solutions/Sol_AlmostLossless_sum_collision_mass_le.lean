-- Prove2me | solution 1 for AlmostLossless.sum_collision_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T13:48:41.367281+00:00
-- url     : https://prove2.me/submissions/dd2ff634-d5bc-4a8b-a171-2a655b1b6b62

import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Definitions.Def_Bridges_MinEntropy
open AlmostLossless NonArchInfoTheory in
theorem solution {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ} (μ : FinProbDist α)
    {H : Fin K → α → Fin M} (hU : Universal2 H) (S A : Finset α) :
    (M : ℝ) * ∑ k : Fin K, setMass μ (A.filter (fun x => Collides H k S x))
      ≤ (K : ℝ) * S.card * setMass μ A := by
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
  exact hsum S A
