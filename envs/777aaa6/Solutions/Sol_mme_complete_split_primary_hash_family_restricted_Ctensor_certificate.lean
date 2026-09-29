-- Prove2me | solution 1 for mme_complete_split_primary_hash_family_restricted_Ctensor_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T22:21:50.780477+00:00
-- url     : https://prove2.me/submissions/19ba85c1-9154-4e78-9b8b-49655b71d105

import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_complete_split_profile_projection
import Theorems.Thm_mme_primary_hash_family_outerExtractionMap_word_eq_zero_of_mismatch
import Theorems.Thm_mme_primary_hash_family_sharedZ_outer_extraction_exact
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
import Theorems.Thm_mme_primary_hash_family_sharedZ_star_grading_components
import Theorems.Thm_mme_coupled_four_block_exact_address_component_certificate

open MME MME.CompleteSplit MME.DWZComponentRestriction
open CoupledCTensorPackaging Module PiTensorProduct BigOperators
open scoped NNReal

universe u

set_option autoImplicit false
set_option warningAsError true

/-- The actual induced shared-Z family survives simultaneous complete-profile
projection whenever every disallowed basis word mismatches every retained
address in its own mode. -/
theorem solution
    {K : Type u} [Field K]
    (q : ℕ) {T : TensorObj K 3} (grading : T.TypeGrading 3)
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] →
      grading.blockTensor σ = 0)
    (h000 : TensorObj.Isomorphic (MMObj K 1 q 1)
      (grading.blockSubtensor ![0, 0, 0]))
    (h111 : TensorObj.Isomorphic (MMObj K 1 q 1)
      (grading.blockSubtensor ![1, 1, 1]))
    (h012 : TensorObj.Isomorphic (MMObj K q 1 q)
      (grading.blockSubtensor ![0, 1, 2]))
    (h102 : TensorObj.Isomorphic (MMObj K q 1 q)
      (grading.blockSubtensor ![1, 0, 2]))
    {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (grade : (i : Fin 3) → ι i → Fin 3)
    (hzero : ∀ (i : Fin 3) (a : Fin 3) (j : ι i), grade i j ≠ a →
      grading.blockProj i a (b i j) = 0)
    {ell : ℕ} (label : (i : Fin 3) → ι i → CompleteWord ell)
    (beta : Fin 3 → Profile ell) (epsilon : ℝ≥0)
    (hmismatch : ∀ (i : Fin 3) (w : PowIndex (ι i) (2 * N)),
      ¬ ApproxConsistent (label i) (beta i) epsilon w →
      ∀ (a : Fin A) (h : Fin H), ∃ r : Fin (2 * N),
        grade i (PowIndex.get (2 * N) w r) ≠
          componentAddress family a h i r) :
    Nonempty
      (CTensorOneHOneFamilyCertificate
        (restrictedPower T b label beta epsilon (2 * N))
        A H (q ^ (4 * G + 2 * L))) := by
  classical
  refine ⟨{
    star := starObj grading family
    restrict := ?_
    certificate := ?_
  }⟩
  · apply mme_restrict_basisAllAllowedSubtensor_of_vanishes
      (T.kronPow (2 * N)) (TensorObj.bigAdd (starObj grading family))
      (fun i ↦ kronPowModeBasis T i (b i) (2 * N))
      (fun i ↦ ApproxConsistent (label i) (beta i) epsilon)
      (outerExtractionMap grading family)
      (mme_primary_hash_family_sharedZ_outer_extraction_exact
        grading family hSupport).1
    intro i w hnot
    exact mme_primary_hash_family_outerExtractionMap_word_eq_zero_of_mismatch
      grading family i (b i) (grade i) (hzero i) w (hmismatch i w hnot)
  · intro a
    have hc : ∀ h : Fin H, ∃ x y z : ℕ,
        TensorObj.Isomorphic (MMObj K x y z)
          (componentObj grading family a h) ∧
        x * y * z = q ^ (4 * G + 2 * L) := by
      intro h
      exact mme_coupled_four_block_exact_address_component_certificate
        q N L G T grading h000 h111 h012 h102
        (componentExactAddress family a h)
    choose x y z hiso hvolume using hc
    have hstar := mme_primary_hash_family_sharedZ_star_grading_components
      grading family a
    exact {
      grading := starGrading grading family a
      supported := hstar.1
      m := x
      n := y
      p := z
      component := fun h ↦ (hiso h).trans (hstar.2 h)
      common_volume := hvolume
    }
