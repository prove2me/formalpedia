-- Prove2me | solution 1 for mme_primary_hash_family_outerExtractionMap_Z_word_eq_zero_of_mismatch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T12:52:36.074157+00:00
-- url     : https://prove2.me/submissions/908e1460-277b-407b-9cc7-a702febdeff0

import Theorems.Thm_mme_primary_hash_family_sharedZ_outer_extraction_exact
import Theorems.Thm_mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch

open MME MME.DWZComponentRestriction PiTensorProduct BigOperators Module
open CoupledCTensorPackaging

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} (grading : T.TypeGrading 3)
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] →
      grading.blockTensor σ = 0)
    {ι : Type u} (b : Basis ι K (T.V 2)) (grade : ι → Fin 3)
    (hzero : ∀ (a : Fin 3) (j : ι), grade j ≠ a →
      grading.blockProj 2 a (b j) = 0)
    (w : PowIndex ι (2 * N))
    (hmismatch : ∀ a : Fin A, ∃ r : Fin (2 * N),
      grade (PowIndex.get (2 * N) w r) ≠
        componentAddress family a (firstFiberIndex family) 2 r) :
    outerExtractionMap grading family 2
        (kronPowModeBasis T 2 b (2 * N) w) = 0 := by
  rw [(mme_primary_hash_family_sharedZ_outer_extraction_exact
    grading family hSupport).2]
  rw [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro a _
  change (gradedBigAddSlot A (starObj grading family) a 2)
    (gradedAddressProj grading (2 * N)
      (componentAddress family a (firstFiberIndex family)) 2
      (kronPowModeBasis T 2 b (2 * N) w)) = 0
  rw [mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch
    grading 2 b grade hzero (2 * N)
    (componentAddress family a (firstFiberIndex family)) w
    (hmismatch a)]
  exact LinearMap.map_zero _
