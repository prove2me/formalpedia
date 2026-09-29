-- Prove2me | Theorems.Thm_mme_little_endian_MM_kron_tensor
-- name    : mme_little_endian_MM_kron_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T04:47:28.802254+00:00
-- url     : https://prove2.me/theorems/ba14d8ce-9fd5-41dd-8c15-73c5cf1d3742
-- title:
--   Exact little-endian multiplicativity of the matrix-multiplication tensor
-- statement:
--   Let $\\langle n,m,p\\rangle$ and $\\langle n^\\prime,m^\\prime,p^\\prime\\rangle$ be matrix-multiplication tensors over a field $K$. Under the explicit little-endian mode equivalences, their Kronecker product is carried exactly to\n\n$$\n\\langle n^\\prime n,\\;m^\\prime m,\\;p^\\prime p\\rangle.\n$$\n\nThe identity is an equality of complete tensors, not only an isomorphism of their mode spaces. The coordinate order is tail before head, so iterating the theorem agrees with the ordinary base expansion of literal channel words.\n\nThis exact coordinate-sensitive multiplicativity is the bridge needed to flatten a power of a central CW-square constituent before retaining a prescribed family of words.\n\n**Formalization Note** The theorem exposes the concrete mode maps, so downstream proofs can combine the complete tensor identity with their separately stated basis laws.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3 and Appendix A, https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_little_endian_MM_coordinate_router

open PiTensorProduct TensorProduct BigOperators
open MME
open MME.DWZFineChannel

universe u

set_option autoImplicit false

theorem mme_little_endian_MM_kron_tensor
    (K : Type u) [Field K]
    (n m p n' m' p' : ℕ) :
    PiTensorProduct.map
        (fun s => (littleEndianModeEquiv K n m p n' m' p' s).toLinearMap)
        (TensorObj.kron (MMObj K n m p) (MMObj K n' m' p')).t =
      (MMObj K (n' * n) (m' * m) (p' * p)).t := by
  sorry
