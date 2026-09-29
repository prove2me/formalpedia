-- Prove2me | solution 2 for UniversalRedundancy.shtarkovSum_tiedProdClass_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T16:37:39.2787+00:00
-- url     : https://prove2.me/submissions/d9bf4406-392e-4867-9043-3226cb3560b9

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {X₁ X₂ : Type*} [Fintype X₁] [Fintype X₂] {Θ : Type*} [Nonempty Θ]
    (S₁ : SourceClass X₁ Θ) (S₂ : SourceClass X₂ Θ) :
    (tiedProdClass S₁ S₂).shtarkovSum ≤ S₁.shtarkovSum * S₂.shtarkovSum := by
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
  unfold SourceClass.shtarkovSum
  calc ∑ x, (tiedProdClass S₁ S₂).maxLik x
      ≤ ∑ x : X₁ × X₂, S₁.maxLik x.1 * S₂.maxLik x.2 := Finset.sum_le_sum (fun x _ => hml x)
    _ = (∑ x₁, S₁.maxLik x₁) * (∑ x₂, S₂.maxLik x₂) := by
        rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
