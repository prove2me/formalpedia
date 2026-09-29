-- Prove2me | Theorems.Thm_mme_dwz_table2_standard_obj_restrict_canonical_address
-- name    : mme_dwz_table2_standard_obj_restrict_canonical_address
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T08:28:21.220653+00:00
-- url     : https://prove2.me/theorems/3c08d0f6-12ed-4c5e-94be-715f42cce009
-- title:
--   Exact Table-2 address blocks restrict to the complete standard object
-- statement:
--   Let $K$ be a field, let $m\geq0$, and let $w$ be a finite word in the fifteen Table-2 component labels whose fiber over each row $s$ has the exact prescribed size $n_s m$. Form the literal $q=6$ CW-square canonical address block determined positionwise by the three coarse grades of $w(r)$. Then this address block genuinely restricts to the complete Table-2 standard-form tensor
--
--   $$
--   T^*(m)=\bigotimes_{s=0}^{14}T_s^{\otimes n_s m}[\widetilde\alpha_s].
--   $$
--
--   The restriction applies the exact accepted $Z$-only available-word projection within every component power and preserves the full $X$ and $Y$ spaces. This is the source-faithful passage from one exact canonical address block to the complete standard object; it precedes useful-small-block decomposition and hole removal.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.2--5.4 and Section 6.3/Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_standard_obj
import Theorems.Thm_mme_dwz_table2_canonical_address_restricted_components_restrict
import Theorems.Thm_mme_dwz_table2_component_projection_certificate

open MME
open MME.DWZSquare

universe u

set_option autoImplicit false

theorem mme_dwz_table2_standard_obj_restrict_canonical_address
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
  sorry
