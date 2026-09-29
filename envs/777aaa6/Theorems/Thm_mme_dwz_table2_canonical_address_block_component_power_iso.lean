-- Prove2me | Theorems.Thm_mme_dwz_table2_canonical_address_block_component_power_iso
-- name    : mme_dwz_table2_canonical_address_block_component_power_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:43:27.723343+00:00
-- url     : https://prove2.me/theorems/ed23eae6-e701-4d7d-9e96-d52b0974d9ee
-- title:
--   A Table-2 address block is the canonical fifteen-component product
-- statement:
--   Let $G$ be the canonical five-grading of $CW_6\otimes CW_6$. For each of the fifteen Table-2 grade triples $s=(i_s,j_s,k_s)$, let $B_s$ be the literal canonical block subtensor $G[i_s,j_s,k_s]$, and let $c_s$ be its exact integral Table-2 count at scale $10^{16}$. If a component word has exactly $c_s m$ positions of type $s$ for every $s$, then its graded address block satisfies
--
--   $$
--   \bigotimes_r B_{\operatorname{word}(r)}
--     \cong
--   \bigotimes_{s=0}^{14} B_s^{\otimes c_s m}.
--   $$
--
--   Thus one concrete Table-2 address block has the fifteen-component power skeleton required by the standard-form tensor $T^*$. Every factor is the actual canonical block subtensor: the statement makes no scalar-dimension substitution and no assertion that fine holes have already been removed or filled.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5: Definition 5.2 (component standard form, PDF p.47 / printed p.46), Section 6.3 and Table 2 (PDF pp.59–60 / printed pp.58–59). The integer multiplicities are the exact scale-10^16 realization of the printed Table-2 distribution.

import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_CW_square_canonical_grading
import Definitions.Def_mme_CW_square_five_grade_certificate
import Theorems.Thm_mme_kronFin_group_by_exact_fibers_iso

open MME
open MME.DWZSquare

universe u

set_option autoImplicit false

theorem mme_dwz_table2_canonical_address_block_component_power_iso
    {K : Type u} [Field K] {N m : ℕ}
    (word : Fin N → Fin 15)
    (hword : ∀ s : Fin 15,
      Fintype.card {r : Fin N // word r = s} =
        MME.DWZTable2Counts.component s * m) :
    let G := cwSquareCanonicalGrading K 6
    let componentBlock : Fin 15 → TensorObj K 3 := fun s ↦
      G.blockSubtensor
        (cwSquareBlockType (shapeX s) (shapeY s) (shapeZ s))
    let address : Fin 3 → Fin N → Fin 5 := fun i r ↦
      cwSquareBlockType
        (shapeX (word r)) (shapeY (word r)) (shapeZ (word r)) i
    TensorObj.Isomorphic
      (gradedAddressBlock G address)
      (TensorObj.kronFin 15 (fun s ↦
        (componentBlock s).kronPow
          (MME.DWZTable2Counts.component s * m))) := by
  sorry
