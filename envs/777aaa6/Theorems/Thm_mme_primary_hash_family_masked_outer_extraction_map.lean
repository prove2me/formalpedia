-- Prove2me | Theorems.Thm_mme_primary_hash_family_masked_outer_extraction_map
-- name    : mme_primary_hash_family_masked_outer_extraction_map
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T05:50:39.823864+00:00
-- url     : https://prove2.me/theorems/cd9498f0-efe7-4981-b874-de9b18f1d6e2
-- title:
--   Primary-family extraction survives compatible word filters
-- statement:
--   Let $T$ have a three-grading supported on $000,111,012,102$, and let a primary coupled-address family have parameters $(N,L,G,A,H)$. Choose graded mode bases and a diagonal word mask in each mode of $T^{\otimes 2N}$. Assume each mask retains every word whose grades agree with any component address of the family. Then the explicit outer extraction maps still produce the direct sum of the family's shared-Z stars from the masked power: $$\bigotimes_i F_i\left((\bigotimes_i M_i)T^{\otimes 2N}\right)=\bigoplus_a\operatorname{Star}_a.$$ This allows filters defined using partial address information, provided every fully matching family word is retained. The conclusion is an exact tensor identity; matrix-block certificates and volume estimates remain separate obligations.
-- source:
--   Primary hash family inducedness and graded address projections.

import Theorems.Thm_mme_primary_hash_family_outer_extraction_map
import Theorems.Thm_mme_gradedAddressProj_comp_word_mask

open MME MME.DWZComponentRestriction PiTensorProduct Module CoupledCTensorPackaging
universe u
set_option autoImplicit false

theorem mme_primary_hash_family_masked_outer_extraction_map
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
      (TensorObj.bigAdd (starObj grading family)).t := by sorry
