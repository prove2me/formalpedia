-- Prove2me | Theorems.Thm_mme_CW_section7_balanced_block_restrict
-- name    : mme_CW_section7_balanced_block_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-23T23:06:31.855257+00:00
-- url     : https://prove2.me/theorems/72bb2f30-0be4-47ed-93ec-25e1e8b73eca
-- title:
--   A balanced Section 7 CW type profile gives a square matrix-product block
-- statement:
--   Let $0\le L\le N$, and consider a supported type sequence in the $3N$-th tensor power of $T_q$. Suppose each of the boundary types $(2,0,0)$, $(0,2,0)$, and $(0,0,2)$ occurs exactly $L$ times, while each of the middle types $(1,0,1)$, $(1,1,0)$, and $(0,1,1)$ occurs exactly $N-L$ times. Then the corresponding block restriction is the square matrix-multiplication tensor
--
--   $$
--   \left\langle q^{N-L},q^{N-L},q^{N-L}\right\rangle.
--   $$
--
--   This is the exact single-entry dimension calculation in the balanced type class used in Section 7 before Salem--Spencer hashing and collision pruning. The full six-type profile is retained because its multinomial count is needed by the next laser milestone.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), Section 7, journal pp. 262--263 (PDF pp. 12--13), especially the six type multiplicities and the matrix product of size <q^(N-L),q^(N-L),q^(N-L)>; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Theorems.Thm_mme_CW_type_sequence_restrict
open MME BigOperators
universe u

theorem mme_CW_section7_balanced_block_restrict
    {K : Type u} [Field K] (q N L : ℕ) (hL : L ≤ N)
    (τ : Fin (3 * N) → Fin 3 × Fin 3 × Fin 3)
    (hτ : ∀ k : Fin (3 * N), τ k ∈ CWSupportPattern)
    (h200 : (Finset.univ.filter (fun k : Fin (3 * N) => τ k = (2, 0, 0))).card = L)
    (h020 : (Finset.univ.filter (fun k : Fin (3 * N) => τ k = (0, 2, 0))).card = L)
    (h002 : (Finset.univ.filter (fun k : Fin (3 * N) => τ k = (0, 0, 2))).card = L)
    (h101 : (Finset.univ.filter (fun k : Fin (3 * N) => τ k = (1, 0, 1))).card = N - L)
    (h110 : (Finset.univ.filter (fun k : Fin (3 * N) => τ k = (1, 1, 0))).card = N - L)
    (h011 : (Finset.univ.filter (fun k : Fin (3 * N) => τ k = (0, 1, 1))).card = N - L) :
    TensorObj.Restrict
      (MMObj K (q ^ (N - L)) (q ^ (N - L)) (q ^ (N - L)))
      ((CWObj K q).kronPow (3 * N)) := by sorry
