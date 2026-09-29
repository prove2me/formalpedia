-- Prove2me | Theorems.Thm_mme_gradedAddressBlock_reindex_perm_iso
-- name    : mme_gradedAddressBlock_reindex_perm_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T07:53:44.20497+00:00
-- url     : https://prove2.me/theorems/01eca7a0-16af-404c-932a-de0c0d35b427
-- title:
--   A tensor-position permutation preserves a graded address block
-- statement:
--   Let a finite tensor power be decomposed into literal graded address blocks, and let a permutation reorder all tensor-power positions simultaneously in the three modes. The address block attached to the reordered address is isomorphic, by ordinary modewise linear restrictions in both directions, to the original address block. This is the tensor-position reindexing required by the standard-form shuffling operation.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 5.7 and Claim 5.9, arXiv:2210.10173v5.

import Theorems.Thm_mme_kronFin_group_by_exact_fibers_iso
import Definitions.Def_mme_induced_word_zeroing

open MME

universe u

set_option autoImplicit false

theorem mme_gradedAddressBlock_reindex_perm_iso
    {K : Type u} [Field K] {T : TensorObj K 3} {t N : ℕ}
    (G : T.TypeGrading t) (address : Fin 3 → Fin N → Fin t)
    (e : Equiv.Perm (Fin N)) :
    TensorObj.Isomorphic
      (gradedAddressBlock G (fun i r ↦ address i (e r)))
      (gradedAddressBlock G address) := by
  sorry
