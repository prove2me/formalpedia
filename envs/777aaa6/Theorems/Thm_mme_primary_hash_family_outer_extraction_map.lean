-- Prove2me | Theorems.Thm_mme_primary_hash_family_outer_extraction_map
-- name    : mme_primary_hash_family_outer_extraction_map
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T05:45:30.817094+00:00
-- url     : https://prove2.me/theorems/cec5516f-c4ff-49b4-95bb-d136687cea5c
-- title:
--   A primary hash family extracts its shared-Z stars from a graded tensor power
-- statement:
--   Let $T$ be a three-mode tensor over a field, with grades $0,1,2$ and support contained in $\{000,111,012,102\}$. Let a primary coupled-address family have parameters $(N,L,G,A,H)$. For each outer index $a$, form a star by summing its $H$ address blocks: X and Y use separate summands indexed by $h$, while Z uses the common Z space of that outer fiber. The explicit outer extraction maps $F_i$, formed by summing address projections followed by the corresponding star and outer inclusions, satisfy $$\bigotimes_{i=0}^2 F_i\bigl(T^{\otimes 2N}\bigr)=\bigoplus_{a=0}^{A-1}\operatorname{Star}_a.$$ The original family's inducedness eliminates all non-diagonal choices. This establishes the tensor identity for the shared-Z family extraction; it does not yet assert the stars' matrix-block certificates or a volume bound.
-- source:
--   Primary hash family inducedness and graded address projections.

import Definitions.Def_mme_coupled_Ctensor_outer_extraction_data
import Mathlib.LinearAlgebra.PiTensorProduct

open MME PiTensorProduct BigOperators CoupledCTensorPackaging
universe u
set_option autoImplicit false

variable {K : Type u} [Field K]

theorem mme_primary_hash_family_outer_extraction_map
    {K : Type u} [Field K] {T : TensorObj K 3}
    (grading : T.TypeGrading 3) {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] → grading.blockTensor σ = 0) :
    PiTensorProduct.map (outerExtractionMap grading family) (T.kronPow (2 * N)).t =
      (TensorObj.bigAdd (starObj grading family)).t := by sorry
