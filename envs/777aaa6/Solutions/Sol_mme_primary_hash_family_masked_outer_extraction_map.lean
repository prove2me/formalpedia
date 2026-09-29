-- Prove2me | solution 1 for mme_primary_hash_family_masked_outer_extraction_map
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T05:50:47.205521+00:00
-- url     : https://prove2.me/submissions/92675499-d469-4b27-9722-ce9e41580ad0

import Theorems.Thm_mme_primary_hash_family_outer_extraction_map
import Theorems.Thm_mme_gradedAddressProj_comp_word_mask

open MME MME.DWZComponentRestriction PiTensorProduct Module CoupledCTensorPackaging
universe u
set_option autoImplicit false

/-- The explicit outer extraction maps survive any word masks retaining all
words whose grades match a family component address. -/
theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3}
    (grading : T.TypeGrading 3) {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] → grading.blockTensor σ = 0)
    {α : Fin 3 → Type u} (b : ∀ i, Basis (α i) K (T.V i))
    (grade : ∀ i, α i → Fin 3)
    (hzero : ∀ i a j, grade i j ≠ a → grading.blockProj i a (b i j) = 0)
    (keep : ∀ i, PowIndex (α i) (2 * N) → Prop) [∀ i, DecidablePred (keep i)]
    (hkeep : ∀ a h i w,
      (∀ r, grade i (PowIndex.get (2 * N) w r) = componentAddress family a h i r) →
      keep i w) :
    let mask := fun i => (kronPowModeBasis T i (b i) (2 * N)).constr K
      (fun w => if keep i w then kronPowModeBasis T i (b i) (2 * N) w else 0)
    PiTensorProduct.map (outerExtractionMap grading family)
        (PiTensorProduct.map mask (T.kronPow (2 * N)).t) =
      (TensorObj.bigAdd (starObj grading family)).t := by
  intro mask
  have hp (a : Fin A) (h : Fin H) (i : Fin 3) :
      (gradedAddressProj grading (2 * N) (componentAddress family a h) i).comp (mask i) =
        gradedAddressProj grading (2 * N) (componentAddress family a h) i :=
    mme_gradedAddressProj_comp_word_mask grading i (b i) (grade i) (hzero i)
      (componentAddress family a h) (keep i) (hkeep a h i)
  have hs (i : Fin 3) (j : outerChoiceType (A := A) (H := H) i) :
      (outerExtractionSummand grading family i j).comp (mask i) =
        outerExtractionSummand grading family i j := by
    apply LinearMap.ext
    intro x
    fin_cases i
    · change gradedBigAddSlot A (starObj grading family) j.1 0
        (componentInclusion grading family j.1 j.2 0
          (gradedAddressProj grading (2 * N) (componentAddress family j.1 j.2) 0 (mask 0 x))) =
        gradedBigAddSlot A (starObj grading family) j.1 0
          (componentInclusion grading family j.1 j.2 0
            (gradedAddressProj grading (2 * N) (componentAddress family j.1 j.2) 0 x))
      congr 1
      congr 1
      exact LinearMap.congr_fun (hp j.1 j.2 0) x
    · change gradedBigAddSlot A (starObj grading family) j.1 1
        (componentInclusion grading family j.1 j.2 1
          (gradedAddressProj grading (2 * N) (componentAddress family j.1 j.2) 1 (mask 1 x))) =
        gradedBigAddSlot A (starObj grading family) j.1 1
          (componentInclusion grading family j.1 j.2 1
            (gradedAddressProj grading (2 * N) (componentAddress family j.1 j.2) 1 x))
      congr 1
      congr 1
      exact LinearMap.congr_fun (hp j.1 j.2 1) x
    · change gradedBigAddSlot A (starObj grading family) j 2
        (gradedAddressProj grading (2 * N) (componentAddress family j (firstFiberIndex family))
          2 (mask 2 x)) =
        gradedBigAddSlot A (starObj grading family) j 2
          (gradedAddressProj grading (2 * N) (componentAddress family j (firstFiberIndex family)) 2 x)
      congr 1
      exact LinearMap.congr_fun (hp j (firstFiberIndex family) 2) x
  have hf (i : Fin 3) : (outerExtractionMap grading family i).comp (mask i) =
      outerExtractionMap grading family i := by
    apply LinearMap.ext
    intro x
    change (∑ j, outerExtractionSummand grading family i j) (mask i x) =
      (∑ j, outerExtractionSummand grading family i j) x
    simp only [LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact LinearMap.congr_fun (hs i j) x
  change (PiTensorProduct.map (outerExtractionMap grading family) ∘ₗ
    PiTensorProduct.map mask) (T.kronPow (2 * N)).t = _
  rw [← PiTensorProduct.map_comp]
  simp only [hf]
  exact mme_primary_hash_family_outer_extraction_map grading family hSupport

#print axioms solution
