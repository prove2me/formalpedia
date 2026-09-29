-- Prove2me | solution 2 for UniversalRedundancy.maxLik_prodClass
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T16:22:30.020684+00:00
-- url     : https://prove2.me/submissions/14d79b86-571c-4fde-a353-0334716f5f91

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {X₁ X₂ : Type*} [Fintype X₁] [Fintype X₂] {Θ₁ Θ₂ : Type*}
    [Fintype Θ₁] [Fintype Θ₂] [Nonempty Θ₁] [Nonempty Θ₂]
    (S₁ : SourceClass X₁ Θ₁) (S₂ : SourceClass X₂ Θ₂) (x : X₁ × X₂) :
    (prodClass S₁ S₂).maxLik x = S₁.maxLik x.1 * S₂.maxLik x.2 := by
  have hb1 : ∀ θ y, S₁.prob θ y ≤ 1 := by
    intro θ y
    rw [← S₁.sum_one θ]
    exact Finset.single_le_sum (f := fun y => S₁.prob θ y) (fun z _ => S₁.nonneg θ z) (Finset.mem_univ y)
  have hb2 : ∀ θ y, S₂.prob θ y ≤ 1 := by
    intro θ y
    rw [← S₂.sum_one θ]
    exact Finset.single_le_sum (f := fun y => S₂.prob θ y) (fun z _ => S₂.nonneg θ z) (Finset.mem_univ y)
  have hbP : ∀ θ y, (prodClass S₁ S₂).prob θ y ≤ 1 := by
    intro θ y
    rw [← (prodClass S₁ S₂).sum_one θ]
    exact Finset.single_le_sum (f := fun y => (prodClass S₁ S₂).prob θ y)
      (fun z _ => (prodClass S₁ S₂).nonneg θ z) (Finset.mem_univ y)
  have hle1 : ∀ θ y, S₁.prob θ y ≤ S₁.maxLik y := fun θ y =>
    le_ciSup (f := fun θ => S₁.prob θ y) ⟨1, by rintro _ ⟨θ, rfl⟩; exact hb1 θ y⟩ θ
  have hle2 : ∀ θ y, S₂.prob θ y ≤ S₂.maxLik y := fun θ y =>
    le_ciSup (f := fun θ => S₂.prob θ y) ⟨1, by rintro _ ⟨θ, rfl⟩; exact hb2 θ y⟩ θ
  have hleP : ∀ θ y, (prodClass S₁ S₂).prob θ y ≤ (prodClass S₁ S₂).maxLik y := fun θ y =>
    le_ciSup (f := fun θ => (prodClass S₁ S₂).prob θ y) ⟨1, by rintro _ ⟨θ, rfl⟩; exact hbP θ y⟩ θ
  obtain ⟨t₁, ht₁⟩ := exists_eq_ciSup_of_finite (f := fun θ => S₁.prob θ x.1)
  obtain ⟨t₂, ht₂⟩ := exists_eq_ciSup_of_finite (f := fun θ => S₂.prob θ x.2)
  have hm1 : S₁.maxLik x.1 = S₁.prob t₁ x.1 := ht₁.symm
  have hm2 : S₂.maxLik x.2 = S₂.prob t₂ x.2 := ht₂.symm
  apply le_antisymm
  · refine ciSup_le (fun θ => ?_)
    show S₁.prob θ.1 x.1 * S₂.prob θ.2 x.2 ≤ S₁.maxLik x.1 * S₂.maxLik x.2
    exact mul_le_mul (hle1 θ.1 x.1) (hle2 θ.2 x.2) (S₂.nonneg θ.2 x.2)
      ((S₁.nonneg θ.1 x.1).trans (hle1 θ.1 x.1))
  · rw [hm1, hm2]
    exact hleP (t₁, t₂) x
