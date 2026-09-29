-- Prove2me | solution 1 for mme_primary_hash_family_outerExtractionMap_word_eq_zero_of_mismatch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T22:17:29.840917+00:00
-- url     : https://prove2.me/submissions/bd4462fd-4b00-4c22-ab88-3b8722646ff0

import Definitions.Def_mme_coupled_Ctensor_outer_extraction_data
import Theorems.Thm_mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch

open MME MME.DWZComponentRestriction PiTensorProduct BigOperators Module
open CoupledCTensorPackaging

universe u

set_option autoImplicit false
set_option warningAsError true

/-- Every mode of the actual directional family extraction kills a word
which mismatches each retained address in that mode. -/
theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} (grading : T.TypeGrading 3)
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (i : Fin 3) {ι : Type u}
    (b : Basis ι K (T.V i)) (grade : ι → Fin 3)
    (hzero : ∀ (a : Fin 3) (j : ι), grade j ≠ a →
      grading.blockProj i a (b j) = 0)
    (w : PowIndex ι (2 * N))
    (hmismatch : ∀ (a : Fin A) (h : Fin H), ∃ r : Fin (2 * N),
      grade (PowIndex.get (2 * N) w r) ≠
        componentAddress family a h i r) :
    outerExtractionMap grading family i
        (kronPowModeBasis T i b (2 * N) w) = 0 := by
  classical
  fin_cases i
  · simp only [outerExtractionMap, LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro p _
    change gradedBigAddSlot A (starObj grading family) p.1 0
      (componentInclusion grading family p.1 p.2 0
        (gradedAddressProj grading (2 * N)
          (componentAddress family p.1 p.2) 0
          (kronPowModeBasis T 0 b (2 * N) w))) = 0
    rw [mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch
      grading 0 b grade hzero (2 * N)
      (componentAddress family p.1 p.2) w (hmismatch p.1 p.2)]
    exact (congrArg (gradedBigAddSlot A (starObj grading family) p.1 0)
      (componentInclusion grading family p.1 p.2 0).map_zero).trans
        (gradedBigAddSlot A (starObj grading family) p.1 0).map_zero
  · simp only [outerExtractionMap, LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro p _
    change gradedBigAddSlot A (starObj grading family) p.1 1
      (componentInclusion grading family p.1 p.2 1
        (gradedAddressProj grading (2 * N)
          (componentAddress family p.1 p.2) 1
          (kronPowModeBasis T 1 b (2 * N) w))) = 0
    rw [mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch
      grading 1 b grade hzero (2 * N)
      (componentAddress family p.1 p.2) w (hmismatch p.1 p.2)]
    exact (congrArg (gradedBigAddSlot A (starObj grading family) p.1 1)
      (componentInclusion grading family p.1 p.2 1).map_zero).trans
        (gradedBigAddSlot A (starObj grading family) p.1 1).map_zero
  · simp only [outerExtractionMap, LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro a _
    change gradedBigAddSlot A (starObj grading family) a 2
      (gradedAddressProj grading (2 * N)
        (componentAddress family a (firstFiberIndex family)) 2
        (kronPowModeBasis T 2 b (2 * N) w)) = 0
    rw [mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch
      grading 2 b grade hzero (2 * N)
      (componentAddress family a (firstFiberIndex family)) w
      (hmismatch a (firstFiberIndex family))]
    exact (gradedBigAddSlot A (starObj grading family) a 2).map_zero
