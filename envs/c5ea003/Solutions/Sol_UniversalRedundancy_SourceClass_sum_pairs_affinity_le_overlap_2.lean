-- Prove2me | solution 2 for UniversalRedundancy.SourceClass.sum_pairs_affinity_le_overlap
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T17:38:32.459495+00:00
-- url     : https://prove2.me/submissions/0364d60b-2d90-44bf-8e5c-e7603a669c1f

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
open UniversalRedundancy UniversalRedundancy.SourceClass Finset in
theorem solution {X : Type*} [Fintype X] {Θ : Type*} [Fintype Θ] [DecidableEq Θ] [Nonempty Θ]
    (S : SourceClass X Θ) :
    ∑ θ : Θ, ∑ θ' ∈ univ.erase θ, (1 - tvDist (S.prob θ) (S.prob θ'))
      ≤ (Fintype.card Θ : ℝ) * ((Fintype.card Θ : ℝ) - 1) * S.overlap := by
  have hle1 : ∀ θ x, S.prob θ x ≤ 1 := by
    intro θ x
    rw [← S.sum_one θ]
    exact Finset.single_le_sum (f := fun x => S.prob θ x) (fun y _ => S.nonneg θ y) (Finset.mem_univ x)
  have hbdd : ∀ x, BddAbove (Set.range fun θ => S.prob θ x) := fun x =>
    ⟨1, by rintro _ ⟨θ, rfl⟩; exact hle1 θ x⟩
  have hle : ∀ θ x, S.prob θ x ≤ S.maxLik x := fun θ x => le_ciSup (hbdd x) θ
  have hml0 : ∀ x, 0 ≤ S.maxLik x := by
    intro x
    obtain ⟨θ₀⟩ := ‹Nonempty Θ›
    exact (S.nonneg θ₀ x).trans (hle θ₀ x)
  have hone_le : 1 ≤ S.shtarkovSum := by
    obtain ⟨θ₀⟩ := ‹Nonempty Θ›
    rw [← S.sum_one θ₀]
    exact Finset.sum_le_sum (fun x _ => hle θ₀ x)
  have hCpos : 0 < S.shtarkovSum := by linarith
  have hmin : ∀ a b : ℝ, min a b = (a + b - |a - b|) / 2 := by
    intro a b
    rcases le_total a b with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]
      ring
  have haff : ∀ θ θ', 1 - tvDist (S.prob θ) (S.prob θ') = ∑ x, min (S.prob θ x) (S.prob θ' x) := by
    intro θ θ'
    unfold tvDist
    simp only [hmin]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, S.sum_one, S.sum_one]
    ring
  have hpt : ∀ θ θ' x, θ ≠ θ' → min (S.prob θ x) (S.prob θ' x) ≤ (∑ t, S.prob t x) - S.maxLik x := by
    intro θ θ' x hne
    obtain ⟨θs, hθs⟩ := exists_eq_ciSup_of_finite (f := fun t => S.prob t x)
    have hm : S.maxLik x = S.prob θs x := hθs.symm
    have herase : ∑ t, S.prob t x - S.prob θs x = ∑ t ∈ univ.erase θs, S.prob t x := by
      rw [← Finset.add_sum_erase univ (fun t => S.prob t x) (Finset.mem_univ θs)]
      ring
    rw [hm, herase]
    by_cases hθ : θ = θs
    · have hmem : θ' ∈ univ.erase θs := Finset.mem_erase.mpr ⟨fun h => hne (hθ.trans h.symm), Finset.mem_univ _⟩
      exact (min_le_right _ _).trans
        (Finset.single_le_sum (f := fun t => S.prob t x) (fun t _ => S.nonneg t x) hmem)
    · have hmem : θ ∈ univ.erase θs := Finset.mem_erase.mpr ⟨hθ, Finset.mem_univ _⟩
      exact (min_le_left _ _).trans
        (Finset.single_le_sum (f := fun t => S.prob t x) (fun t _ => S.nonneg t x) hmem)
  have hterm : ∀ θ θ', θ ≠ θ' → 1 - tvDist (S.prob θ) (S.prob θ') ≤ S.overlap := by
    intro θ θ' hne
    rw [haff]
    unfold SourceClass.overlap
    exact Finset.sum_le_sum (fun x _ => hpt θ θ' x hne)
  have hcard : ((univ.erase (Classical.arbitrary Θ)).card : ℝ) = (Fintype.card Θ : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Nat.cast_sub Fintype.card_pos]
    norm_num
  calc ∑ θ : Θ, ∑ θ' ∈ univ.erase θ, (1 - tvDist (S.prob θ) (S.prob θ'))
      ≤ ∑ θ : Θ, ∑ _θ' ∈ univ.erase θ, S.overlap :=
        Finset.sum_le_sum (fun θ _ => Finset.sum_le_sum (fun θ' hθ' =>
          hterm θ θ' (Finset.ne_of_mem_erase hθ').symm))
    _ = (Fintype.card Θ : ℝ) * ((Fintype.card Θ : ℝ) - 1) * S.overlap := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hc : ∀ θ : Θ, ((univ.erase θ).card : ℝ) = (Fintype.card Θ : ℝ) - 1 := by
          intro θ
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Nat.cast_sub Fintype.card_pos]
          norm_num
        simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
