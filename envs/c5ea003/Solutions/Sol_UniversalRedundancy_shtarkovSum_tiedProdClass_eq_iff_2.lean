-- Prove2me | solution 2 for UniversalRedundancy.shtarkovSum_tiedProdClass_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T17:20:36.870478+00:00
-- url     : https://prove2.me/submissions/ee545501-8c38-4f57-855b-d751ed54c2bd

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {X₁ X₂ : Type*} [Fintype X₁] [Fintype X₂] {Θ : Type*} [Fintype Θ] [Nonempty Θ]
    (S₁ : SourceClass X₁ Θ) (S₂ : SourceClass X₂ Θ) :
    (tiedProdClass S₁ S₂).shtarkovSum = S₁.shtarkovSum * S₂.shtarkovSum ↔
      ∀ x₁ x₂, ∃ θ : Θ, S₁.prob θ x₁ = S₁.maxLik x₁ ∧ S₂.prob θ x₂ = S₂.maxLik x₂ := by
  have hb1 : ∀ θ y, S₁.prob θ y ≤ 1 := by
    intro θ y
    rw [← S₁.sum_one θ]
    exact Finset.single_le_sum (f := fun y => S₁.prob θ y) (fun z _ => S₁.nonneg θ z) (Finset.mem_univ y)
  have hb2 : ∀ θ y, S₂.prob θ y ≤ 1 := by
    intro θ y
    rw [← S₂.sum_one θ]
    exact Finset.single_le_sum (f := fun y => S₂.prob θ y) (fun z _ => S₂.nonneg θ z) (Finset.mem_univ y)
  have hle1 : ∀ θ y, S₁.prob θ y ≤ S₁.maxLik y := fun θ y =>
    le_ciSup (f := fun θ => S₁.prob θ y) ⟨1, by rintro _ ⟨θ, rfl⟩; exact hb1 θ y⟩ θ
  have hle2 : ∀ θ y, S₂.prob θ y ≤ S₂.maxLik y := fun θ y =>
    le_ciSup (f := fun θ => S₂.prob θ y) ⟨1, by rintro _ ⟨θ, rfl⟩; exact hb2 θ y⟩ θ
  have hml : ∀ x : X₁ × X₂, (tiedProdClass S₁ S₂).maxLik x ≤ S₁.maxLik x.1 * S₂.maxLik x.2 :=
    fun x => ciSup_le (fun θ => by
      show S₁.prob θ x.1 * S₂.prob θ x.2 ≤ S₁.maxLik x.1 * S₂.maxLik x.2
      exact mul_le_mul (hle1 θ x.1) (hle2 θ x.2) (S₂.nonneg θ x.2)
        ((S₁.nonneg θ x.1).trans (hle1 θ x.1)))
  have hprod : ∑ x : X₁ × X₂, S₁.maxLik x.1 * S₂.maxLik x.2 = S₁.shtarkovSum * S₂.shtarkovSum := by
    unfold SourceClass.shtarkovSum
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  have hbT : ∀ θ y, (tiedProdClass S₁ S₂).prob θ y ≤ 1 := by
    intro θ y
    rw [← (tiedProdClass S₁ S₂).sum_one θ]
    exact Finset.single_le_sum (f := fun y => (tiedProdClass S₁ S₂).prob θ y)
      (fun z _ => (tiedProdClass S₁ S₂).nonneg θ z) (Finset.mem_univ y)
  have hleT : ∀ θ y, (tiedProdClass S₁ S₂).prob θ y ≤ (tiedProdClass S₁ S₂).maxLik y := fun θ y =>
    le_ciSup (f := fun θ => (tiedProdClass S₁ S₂).prob θ y) ⟨1, by rintro _ ⟨θ, rfl⟩; exact hbT θ y⟩ θ
  have hm1 : ∀ y, 0 ≤ S₁.maxLik y := fun y =>
    (S₁.nonneg (Classical.arbitrary Θ) y).trans (hle1 _ y)
  have hm2 : ∀ y, 0 ≤ S₂.maxLik y := fun y =>
    (S₂.nonneg (Classical.arbitrary Θ) y).trans (hle2 _ y)
  constructor
  · intro hC x₁ x₂
    have hpt : (tiedProdClass S₁ S₂).maxLik (x₁, x₂) = S₁.maxLik x₁ * S₂.maxLik x₂ := by
      have hsum : ∑ x, (tiedProdClass S₁ S₂).maxLik x = ∑ x : X₁ × X₂, S₁.maxLik x.1 * S₂.maxLik x.2 := by
        rw [hprod]
        exact hC
      exact (Finset.sum_eq_sum_iff_of_le (fun x _ => hml x)).mp hsum (x₁, x₂) (Finset.mem_univ _)
    obtain ⟨θs, hθs⟩ := exists_eq_ciSup_of_finite (f := fun θ => (tiedProdClass S₁ S₂).prob θ (x₁, x₂))
    have hts : S₁.prob θs x₁ * S₂.prob θs x₂ = S₁.maxLik x₁ * S₂.maxLik x₂ := by
      have : (tiedProdClass S₁ S₂).prob θs (x₁, x₂) = (tiedProdClass S₁ S₂).maxLik (x₁, x₂) := hθs
      rw [hpt] at this
      exact this
    have ha1 := hle1 θs x₁
    have ha2 := hle2 θs x₂
    have hn1 := S₁.nonneg θs x₁
    have hn2 := S₂.nonneg θs x₂
    by_cases hz1 : S₁.maxLik x₁ = 0
    · obtain ⟨t, ht⟩ := exists_eq_ciSup_of_finite (f := fun θ => S₂.prob θ x₂)
      refine ⟨t, ?_, ht⟩
      have := hle1 t x₁
      have := S₁.nonneg t x₁
      linarith
    by_cases hz2 : S₂.maxLik x₂ = 0
    · obtain ⟨t, ht⟩ := exists_eq_ciSup_of_finite (f := fun θ => S₁.prob θ x₁)
      refine ⟨t, ht, ?_⟩
      have := hle2 t x₂
      have := S₂.nonneg t x₂
      linarith
    have hp1 : 0 < S₁.maxLik x₁ := lt_of_le_of_ne (hm1 x₁) (Ne.symm hz1)
    have hp2 : 0 < S₂.maxLik x₂ := lt_of_le_of_ne (hm2 x₂) (Ne.symm hz2)
    refine ⟨θs, ?_, ?_⟩
    · by_contra hne
      have hlt : S₁.prob θs x₁ < S₁.maxLik x₁ := lt_of_le_of_ne ha1 hne
      nlinarith
    · by_contra hne
      have hlt : S₂.prob θs x₂ < S₂.maxLik x₂ := lt_of_le_of_ne ha2 hne
      nlinarith
  · intro hall
    rw [← hprod]
    unfold SourceClass.shtarkovSum
    refine Finset.sum_congr rfl (fun x _ => le_antisymm (hml x) ?_)
    obtain ⟨θ, h1, h2⟩ := hall x.1 x.2
    have := hleT θ x
    have hx : (tiedProdClass S₁ S₂).prob θ x = S₁.prob θ x.1 * S₂.prob θ x.2 := rfl
    rw [hx, h1, h2] at this
    exact this
