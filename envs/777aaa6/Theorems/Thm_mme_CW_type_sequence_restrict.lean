-- Prove2me | Theorems.Thm_mme_CW_type_sequence_restrict
-- name    : mme_CW_type_sequence_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-23T22:49:20.061355+00:00
-- url     : https://prove2.me/theorems/eedc13de-dd91-4a9e-b0d4-8f329c363020
-- title:
--   Each CW support-type sequence yields its exact matrix-product restriction
-- statement:
--   Let $T_q$ be the Coppersmith--Winograd tensor, and choose at each of $N$ tensor-power positions one of its six support types. Write $n_{abc}$ for the number of positions of type $(a,b,c)$. If every chosen type lies in the CW support, then $T_q^{\otimes N}$ restricts to the rectangular matrix-multiplication tensor
--
--   $$
--   \left\langle q^{n_{101}},q^{n_{110}},q^{n_{011}}\right\rangle.
--   $$
--
--   The order of `TensorObj.Restrict` is target first and source second: the displayed matrix product is obtained from the CW tensor power by modewise linear substitutions. This theorem gives the exact per-type block produced before the Salem--Spencer pruning step of the laser method.
--
--   **Formalization Note** The theorem is valid for $N=0$ and imposes no characteristic restriction on the field.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), Section 7, journal pp. 262--263 (PDF pp. 12--13), and Section 8 block table, journal p. 266 (PDF p. 16); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Theorems.Thm_mme_CW_block_kronPow_MM_corrected
import Theorems.Thm_mme_CW_block_dimension_products
open MME BigOperators
universe u

theorem mme_CW_type_sequence_restrict {K : Type u} [Field K] (q N : ℕ)
    (τ : Fin N → Fin 3 × Fin 3 × Fin 3)
    (hτ : ∀ k : Fin N, τ k ∈ CWSupportPattern) :
    TensorObj.Restrict
      (MMObj K
        (q ^ (Finset.univ.filter (fun k : Fin N => τ k = (1, 0, 1))).card)
        (q ^ (Finset.univ.filter (fun k : Fin N => τ k = (1, 1, 0))).card)
        (q ^ (Finset.univ.filter (fun k : Fin N => τ k = (0, 1, 1))).card))
      ((CWObj K q).kronPow N) := by sorry
