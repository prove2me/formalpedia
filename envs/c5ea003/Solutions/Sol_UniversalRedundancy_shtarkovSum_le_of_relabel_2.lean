-- Prove2me | solution 2 for UniversalRedundancy.shtarkovSum_le_of_relabel
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T17:33:52.494098+00:00
-- url     : https://prove2.me/submissions/3038cc62-0c04-4d65-abfe-f8f505de7a1a

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {X Y Θ Ξ : Type*} [Fintype X] [Fintype Y]
    [Nonempty Θ] [Nonempty Ξ] (S : SourceClass X Θ) (T : SourceClass Y Ξ)
    (e : X ≃ Y) (ι : Θ → Ξ) (hcomp : ∀ θ x, S.prob θ x = T.prob (ι θ) (e x)) :
    S.shtarkovSum ≤ T.shtarkovSum := by
  have hbT : ∀ ξ y, T.prob ξ y ≤ 1 := by
    intro ξ y
    rw [← T.sum_one ξ]
    exact Finset.single_le_sum (f := fun y => T.prob ξ y) (fun z _ => T.nonneg ξ z) (Finset.mem_univ y)
  have hleT : ∀ ξ y, T.prob ξ y ≤ T.maxLik y := fun ξ y =>
    le_ciSup (f := fun ξ => T.prob ξ y) ⟨1, by rintro _ ⟨ξ, rfl⟩; exact hbT ξ y⟩ ξ
  unfold SourceClass.shtarkovSum
  calc ∑ x, S.maxLik x ≤ ∑ x, T.maxLik (e x) :=
        Finset.sum_le_sum (fun x _ => ciSup_le (fun θ => by
          show S.prob θ x ≤ T.maxLik (e x)
          rw [hcomp]
          exact hleT (ι θ) (e x)))
    _ = ∑ y, T.maxLik y := Equiv.sum_comp e (fun y => T.maxLik y)
