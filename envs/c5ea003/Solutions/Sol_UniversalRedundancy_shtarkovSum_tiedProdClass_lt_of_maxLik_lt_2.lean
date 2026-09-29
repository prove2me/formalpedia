-- Prove2me | solution 2 for UniversalRedundancy.shtarkovSum_tiedProdClass_lt_of_maxLik_lt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T17:14:48.005803+00:00
-- url     : https://prove2.me/submissions/d774afb4-7559-4a4d-9d40-c63dfeaa6b73

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {X₁ X₂ : Type*} [Fintype X₁] [Fintype X₂] {Θ : Type*} [Nonempty Θ]
    (S₁ : SourceClass X₁ Θ) (S₂ : SourceClass X₂ Θ) {x₁ : X₁} {x₂ : X₂}
    (h : (tiedProdClass S₁ S₂).maxLik (x₁, x₂) < S₁.maxLik x₁ * S₂.maxLik x₂) :
    (tiedProdClass S₁ S₂).shtarkovSum < S₁.shtarkovSum * S₂.shtarkovSum := by
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
  rw [← hprod]
  unfold SourceClass.shtarkovSum
  exact Finset.sum_lt_sum (fun x _ => hml x) ⟨(x₁, x₂), Finset.mem_univ _, h⟩
