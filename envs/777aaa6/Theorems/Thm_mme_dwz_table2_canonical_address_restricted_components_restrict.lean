-- Prove2me | Theorems.Thm_mme_dwz_table2_canonical_address_restricted_components_restrict
-- name    : mme_dwz_table2_canonical_address_restricted_components_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T07:34:43.870158+00:00
-- url     : https://prove2.me/theorems/cf0ff0a4-4c10-438e-9d38-2f089897a4b2
-- title:
--   Restricted Table-2 components assemble inside the canonical address block
-- statement:
--   For a component word with the exact integral Table-2 histogram, suppose that each of the fifteen selected component tensors genuinely restricts from the corresponding canonical CW-square component power. Then their ordered Kronecker product genuinely restricts from the literal source address block of that word. This is the tensor-semantic assembly step needed after the Z-only restricted-splitting projections.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5: Definitions 5.2--5.4 and Section 6.3/Table 2.

import Theorems.Thm_mme_dwz_table2_canonical_address_block_component_power_iso
import Definitions.Def_mme_rank_bridge

open MME
open MME.DWZSquare

universe u

set_option autoImplicit false

theorem mme_dwz_table2_canonical_address_restricted_components_restrict
    {K : Type u} [Field K] {N m : ℕ}
    (word : Fin N → Fin 15)
    (hword : ∀ s : Fin 15,
      Fintype.card {r : Fin N // word r = s} =
        MME.DWZTable2Counts.component s * m)
    (selected : Fin 15 → TensorObj K 3)
    (hselected : ∀ s : Fin 15,
      TensorObj.Restrict (selected s)
        (((cwSquareCanonicalGrading K 6).blockSubtensor
          (cwSquareBlockType (shapeX s) (shapeY s) (shapeZ s))).kronPow
            (MME.DWZTable2Counts.component s * m))) :
    let address : Fin 3 → Fin N → Fin 5 := fun i r ↦
      cwSquareBlockType
        (shapeX (word r)) (shapeY (word r)) (shapeZ (word r)) i
    TensorObj.Restrict
      (TensorObj.kronFin 15 selected)
      (gradedAddressBlock (cwSquareCanonicalGrading K 6) address) := by
  sorry
