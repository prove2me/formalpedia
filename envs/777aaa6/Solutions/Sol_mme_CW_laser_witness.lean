-- Prove2me | solution 1 for mme_CW_laser_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-31T19:18:35.387191+00:00
-- url     : https://prove2.me/submissions/60ca2df1-978f-4046-a1f1-98c25800149b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_CW_canonical_aligned_witness
import Theorems.Thm_mme_CW_support_pattern_symmetric
import Theorems.Thm_mme_CW_value_ge_at_q6
import Definitions.Def_mme_CW_support_pattern

open MME

universe u

theorem solution {K : Type u} [Field K] :
    ∃ (G : (CWObj K 6).TypeGrading 3) (S : Finset (Fin 3 × Fin 3 × Fin 3)),
      LaserSymmetric S ∧
      TensorObj.LaserAlignedSupport G S ∧
      (5 : ℝ) / 2 ≤ laserValueFormula G S := by
  obtain ⟨G, hAlign⟩ := mme_CW_canonical_aligned_witness (K := K) 6
  refine ⟨G, CWSupportPattern, mme_CW_support_pattern_symmetric, hAlign, ?_⟩
  exact mme_CW_value_ge_at_q6 G hAlign
