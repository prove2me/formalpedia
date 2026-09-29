-- Prove2me | Theorems.Thm_mme_CW_block_dimension_products
-- name    : mme_CW_block_dimension_products
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-23T22:46:22.434323+00:00
-- url     : https://prove2.me/theorems/f9d23d4f-b2d8-43ea-b1e8-53c03c3ef1d9
-- title:
--   CW block dimensions are powers of q determined by type counts
-- statement:
--   Let $q,N$ be natural numbers and let $\tau$ be a length-$N$ sequence of CW block types. The six CW support types have matrix-multiplication dimensions $(1,1,q)$, $(q,1,1)$, $(1,q,1)$, and three copies of $(1,1,1)$. Consequently, the coordinatewise product of the dimensions along $\tau$ is
--
--   $$
--   \left(q^{n_{101}},q^{n_{110}},q^{n_{011}}\right),
--   $$
--
--   where $n_{abc}$ is the number of positions of type $(a,b,c)$. The theorem asserts all three coordinate identities exactly, including the empty-sequence case $N=0$.
--
--   This is the block-dimension bookkeeping used when a type sequence in a tensor power of the Coppersmith--Winograd tensor is identified with a single rectangular matrix-multiplication tensor.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), Section 8, journal p. 266 (PDF p. 16), block types (a)--(d); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Theorems.Thm_mme_CW_block_kronPow_MM_corrected
open BigOperators

theorem mme_CW_block_dimension_products (q N : ℕ) (τ : Fin N → Fin 3 × Fin 3 × Fin 3) :
    (∏ k : Fin N, (cwBlockMMDim (τ k) q).1) =
        q ^ (Finset.univ.filter (fun k : Fin N => τ k = (1, 0, 1))).card ∧
    (∏ k : Fin N, (cwBlockMMDim (τ k) q).2.1) =
        q ^ (Finset.univ.filter (fun k : Fin N => τ k = (1, 1, 0))).card ∧
    (∏ k : Fin N, (cwBlockMMDim (τ k) q).2.2) =
        q ^ (Finset.univ.filter (fun k : Fin N => τ k = (0, 1, 1))).card := by sorry
