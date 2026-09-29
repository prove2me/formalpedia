-- Prove2me | Theorems.Thm_mme_CW_2376_exact_address_block_restrict_profile_core
-- name    : mme_CW_2376_exact_address_block_restrict_profile_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T17:33:12.145845+00:00
-- url     : https://prove2.me/theorems/3fae2374-ffc6-4855-9c94-802a22e9ed3f
-- title:
--   An exact CW address block contains the common profile core
-- statement:
--   Let $a$ be any exact-profile address at scale $m$. The ordered Kronecker product $B(a)$ of its graded tensor-square constituents restricts to the common CW profile core:
--
--   $$
--   \operatorname{Core}_m\;\le\;B(a),
--   $$
--
--   where the matrix-multiplication side is $12^{75{,}036m}38^{307{,}638m}$ and the coupled factor is the $616{,}627m$-th power of the cyclic symmetrization of the $(1,1,2)$ constituent.
--
--   The proof may reorder Kronecker factors up to tensor isomorphism. The three coupled joint types occur equally often, so they group into the cyclic coupled certificate; the scalar, rectangular, and central multiplicities give the stated matrix-multiplication dimensions.
--
--   This theorem contains only exact-profile multiplicity and constituent tensor algebra. It is independent of hashing and variable zeroing.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), tensor-square constituent identifications on journal pp. 265--266 and exact multiplicities (13) on pp. 267--269; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_2376_address_block
open MME
universe u

theorem mme_CW_2376_exact_address_block_restrict_profile_core
    {K : Type u} [Field K]
    (cert : CWSquareFiveGradeCertificate K 6)
    (m : ℕ) (a : CW2376ExactProfileAddress m) :
    TensorObj.Restrict (cw2376ProfileCore K m)
      (cw2376ExactAddressBlock cert a) := by
  sorry
