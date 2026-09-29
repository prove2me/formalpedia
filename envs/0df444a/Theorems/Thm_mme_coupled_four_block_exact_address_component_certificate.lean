-- Prove2me | Theorems.Thm_mme_coupled_four_block_exact_address_component_certificate
-- name    : mme_coupled_four_block_exact_address_component_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T04:56:06.7545+00:00
-- url     : https://prove2.me/theorems/87bc462f-3de8-47be-aead-ba011b0c1bf1
-- title:
--   Every exact coupled address block is a matrix-multiplication tensor of the common CW volume
-- statement:
--   Fix a three-graded tensor whose four coupled blocks are two-sided isomorphic to the matrix-multiplication tensors $\langle 1,q,1\rangle$, $\langle 1,q,1\rangle$, $\langle q,1,q\rangle$, and $\langle q,1,q\rangle$. For any length-$2N$ exact-profile address with third-mode multiplicities $L,L,2G$, its ordered tensor block is isomorphic to some matrix-multiplication tensor $\langle m,n,p\rangle$, and its component volume is
--
--   $$
--     mnp=q^{4G+2L}.
--   $$
--
--   The dimensions may depend on the address and its coordinate ordering. Only their product is fixed. This is the componentwise algebra needed to package a shared-$Z$ hash fiber as a source-faithful C-tensor without choosing one common fine survivor identification.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270--271, exact-profile C-tensor components.

import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_induced_word_zeroing
import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_kronFin_respects_iso

open MME PiTensorProduct BigOperators

universe u

theorem mme_coupled_four_block_exact_address_component_certificate
    {K : Type u} [Field K]
    (q N L G : ℕ)
    (T : TensorObj K 3) (grading : T.TypeGrading 3)
    (h000 : TensorObj.Isomorphic (MMObj K 1 q 1)
      (grading.blockSubtensor ![0, 0, 0]))
    (h111 : TensorObj.Isomorphic (MMObj K 1 q 1)
      (grading.blockSubtensor ![1, 1, 1]))
    (h012 : TensorObj.Isomorphic (MMObj K q 1 q)
      (grading.blockSubtensor ![0, 1, 2]))
    (h102 : TensorObj.Isomorphic (MMObj K q 1 q)
      (grading.blockSubtensor ![1, 0, 2]))
    (address : CWQ6ExactCoupledAddress N L G) :
    ∃ m n p : ℕ,
      TensorObj.Isomorphic (MMObj K m n p)
        (gradedAddressBlock grading address.1) ∧
      m * n * p = q ^ (4 * G + 2 * L) := by
  sorry
