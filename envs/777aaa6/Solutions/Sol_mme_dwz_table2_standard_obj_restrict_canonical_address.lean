-- Prove2me | solution 1 for mme_dwz_table2_standard_obj_restrict_canonical_address
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T08:28:29.041329+00:00
-- url     : https://prove2.me/submissions/26dcca9f-f2a9-42c9-88cb-65b949b400a5

import Definitions.Def_mme_dwz_table2_standard_obj
import Theorems.Thm_mme_dwz_table2_canonical_address_restricted_components_restrict
import Theorems.Thm_mme_dwz_table2_component_projection_certificate

open MME
open MME.DWZSquare

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {N m : ℕ}
    (word : Fin N → Fin 15)
    (hword : ∀ s : Fin 15,
      Fintype.card {r : Fin N // word r = s} =
        MME.DWZTable2Counts.component s * m) :
    let address : Fin 3 → Fin N → Fin 5 := fun i r ↦
      cwSquareBlockType
        (shapeX (word r)) (shapeY (word r)) (shapeZ (word r)) i
    TensorObj.Restrict
      (MME.DWZComponentRestriction.dwzTable2StandardObj K m)
      (gradedAddressBlock (cwSquareCanonicalGrading K 6) address) := by
  classical
  simpa only [MME.DWZComponentRestriction.dwzTable2StandardObj] using
    (mme_dwz_table2_canonical_address_restricted_components_restrict
      (K := K) word hword
      (fun s ↦ MME.DWZComponentRestriction.restrictedComponentPower K s m)
      (fun s ↦ (mme_dwz_table2_component_projection_certificate
        (K := K) s m).1))
