-- Prove2me | solution 2 for UniversalRedundancy.SourceClass.shtarkovSum_reindex_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T16:16:31.77524+00:00
-- url     : https://prove2.me/submissions/bbb2fe98-5595-4378-9482-5e16c4b7379b

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {X : Type*} [Fintype X] {Θ : Type*} {Θ' : Type*} [Nonempty Θ] [Nonempty Θ']
    (S : SourceClass X Θ) (ι : Θ' → Θ) :
    (SourceClass.mk (fun θ' x => S.prob (ι θ') x) (fun θ' x => S.nonneg (ι θ') x)
      (fun θ' => S.sum_one (ι θ'))).shtarkovSum ≤ S.shtarkovSum := by
  have hle1 : ∀ θ x, S.prob θ x ≤ 1 := by
    intro θ x
    rw [← S.sum_one θ]
    exact Finset.single_le_sum (f := fun x => S.prob θ x) (fun y _ => S.nonneg θ y) (Finset.mem_univ x)
  have hbdd : ∀ x, BddAbove (Set.range fun θ => S.prob θ x) := fun x =>
    ⟨1, by rintro _ ⟨θ, rfl⟩; exact hle1 θ x⟩
  unfold SourceClass.shtarkovSum SourceClass.maxLik
  exact Finset.sum_le_sum (fun x _ => ciSup_le (fun θ' => le_ciSup (hbdd x) (ι θ')))
