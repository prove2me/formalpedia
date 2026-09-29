-- Prove2me | solution 2 for UniversalRedundancy.shtarkovSum_iidClass_eq_card_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T15:53:25.473815+00:00
-- url     : https://prove2.me/submissions/1a3c6161-3dd1-49c0-930a-d8d6a307cf5c

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] :
    (iidClass A 1).shtarkovSum = (Fintype.card A : ℝ) := by
  have hle1 : ∀ (θ : Simplex A) (x : Fin 1 → A), (iidClass A 1).prob θ x ≤ 1 := by
    intro θ x
    rw [← (iidClass A 1).sum_one θ]
    exact Finset.single_le_sum (f := fun y => (iidClass A 1).prob θ y)
      (fun y _ => (iidClass A 1).nonneg θ y) (Finset.mem_univ x)
  have hml : ∀ x : Fin 1 → A, (iidClass A 1).maxLik x = 1 := by
    intro x
    have hb : BddAbove (Set.range fun θ => (iidClass A 1).prob θ x) :=
      ⟨1, by rintro _ ⟨θ, rfl⟩; exact hle1 θ x⟩
    apply le_antisymm
    · exact ciSup_le (fun θ => hle1 θ x)
    · let δ : Simplex A := ⟨fun a => if a = x 0 then 1 else 0,
        fun a => by dsimp only; split_ifs <;> norm_num, by simp⟩
      have hδ : (iidClass A 1).prob δ x = 1 := by
        simp [iidClass, δ]
      calc (1 : ℝ) = (iidClass A 1).prob δ x := hδ.symm
        _ ≤ (iidClass A 1).maxLik x := le_ciSup hb δ
  unfold SourceClass.shtarkovSum
  simp only [hml, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  simp
