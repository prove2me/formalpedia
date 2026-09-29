-- Prove2me | solution 2 for UniversalRedundancy.shtarkovSum_tiedProdClass_pointMass
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T16:50:18.668983+00:00
-- url     : https://prove2.me/submissions/2d223c67-88a9-42c8-b5b0-02b58f2b7b72

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] :
    (tiedProdClass (pointMassClass A) (pointMassClass A)).shtarkovSum
      = (Fintype.card A : ℝ) := by
  set T := tiedProdClass (pointMassClass A) (pointMassClass A) with hT
  have hb : ∀ a x, T.prob a x ≤ 1 := by
    intro a x
    rw [← T.sum_one a]
    exact Finset.single_le_sum (f := fun y => T.prob a y) (fun z _ => T.nonneg a z) (Finset.mem_univ x)
  have hleT : ∀ a x, T.prob a x ≤ T.maxLik x := fun a x =>
    le_ciSup (f := fun a => T.prob a x) ⟨1, by rintro _ ⟨a, rfl⟩; exact hb a x⟩ a
  have hprob : ∀ a (x : A × A), T.prob a x = (if x.1 = a then 1 else 0) * (if x.2 = a then 1 else 0) := by
    intro a x
    rfl
  have hml : ∀ x : A × A, T.maxLik x = if x.1 = x.2 then 1 else 0 := by
    intro x
    apply le_antisymm
    · refine ciSup_le (fun a => ?_)
      show T.prob a x ≤ _
      rw [hprob]
      by_cases h1 : x.1 = a <;> by_cases h2 : x.2 = a <;> by_cases h3 : x.1 = x.2 <;> simp_all
    · split_ifs with h
      · have := hleT x.1 x
        rw [hprob] at this
        simpa [h] using this
      · exact (T.nonneg x.1 x).trans (hleT x.1 x)
  unfold SourceClass.shtarkovSum
  simp only [hml]
  rw [Fintype.sum_prod_type]
  simp [Finset.sum_ite_eq]
