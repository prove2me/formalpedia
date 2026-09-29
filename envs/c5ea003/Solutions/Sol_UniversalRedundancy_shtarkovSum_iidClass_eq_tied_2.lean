-- Prove2me | solution 2 for UniversalRedundancy.shtarkovSum_iidClass_eq_tied
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T17:27:38.199979+00:00
-- url     : https://prove2.me/submissions/7f4adbbe-506c-4964-95df-a0eec7979337

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] (n₁ n₂ : ℕ) :
    (iidClass A (n₁ + n₂)).shtarkovSum
      = (tiedProdClass (iidClass A n₁) (iidClass A n₂)).shtarkovSum := by
  have hprob : ∀ (θ : Simplex A) (y : Fin n₁ → A) (z : Fin n₂ → A),
      (iidClass A (n₁ + n₂)).prob θ (Fin.append y z)
        = (tiedProdClass (iidClass A n₁) (iidClass A n₂)).prob θ (y, z) := by
    intro θ y z
    show ∏ i, θ.1 (Fin.append y z i) = (∏ i, θ.1 (y i)) * ∏ j, θ.1 (z j)
    rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  have hml : ∀ (y : Fin n₁ → A) (z : Fin n₂ → A),
      (iidClass A (n₁ + n₂)).maxLik (Fin.append y z)
        = (tiedProdClass (iidClass A n₁) (iidClass A n₂)).maxLik (y, z) := by
    intro y z
    unfold SourceClass.maxLik
    congr 1
    funext θ
    exact hprob θ y z
  unfold SourceClass.shtarkovSum
  rw [← Equiv.sum_comp (Fin.appendEquiv n₁ n₂)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  exact hml p.1 p.2
