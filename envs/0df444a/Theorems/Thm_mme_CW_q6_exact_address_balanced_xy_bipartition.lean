-- Prove2me | Theorems.Thm_mme_CW_q6_exact_address_balanced_xy_bipartition
-- name    : mme_CW_q6_exact_address_balanced_xy_bipartition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:41:31.822225+00:00
-- url     : https://prove2.me/theorems/92724b13-33b3-45ae-9683-daed21384a36
-- title:
--   Balanced two-source position reindexing for exact coupled q=6 addresses
-- statement:
--   Let an exact coupled q=6 address have parameter $2n$, hence $4n$ tensor-power positions, and profile parameters $L,G$ satisfying $L+G=2n$. There is a permutation of its positions into two source words of length $2n$. In the first word, the mode-zero grades have multiplicities $(n,n,0)$; in the second word, the mode-one grades have multiplicities $(n,n,0)$.
--
--   Equivalently, there is a bijection $e$ from two labelled copies of a $2n$-element set onto all $4n$ positions such that the left copy meets each of the mode-zero grade-$0$ and grade-$1$ fibers in $n$ positions, while the right copy meets each of the corresponding mode-one fibers in $n$ positions; neither copy uses grade $2$ in its designated mode.
--
--   This is the exact finite reindexing needed to concatenate the two allowed 121/211 source words into one balanced coupled address.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), coupled four-block profile on pp. 270-271; applied to the paired 121/211 construction in Duan--Wu--Zhou, arXiv:2210.10173v5, Section 6.3.

import Mathlib.Tactic
import Definitions.Def_mme_CW_q6_primary_hash_family

open MME

set_option autoImplicit false

theorem mme_CW_q6_exact_address_balanced_xy_bipartition
    {n L G : ℕ} (hLG : L + G = 2 * n)
    (address : CWQ6ExactCoupledAddress (2 * n) L G) :
    ∃ e : (Fin (2 * n) ⊕ Fin (2 * n)) ≃ Fin (2 * (2 * n)),
      (∀ r : Fin 3,
        Fintype.card {j : Fin (2 * n) //
          address.1 0 (e (Sum.inl j)) = r} =
            if r = 0 then n else if r = 1 then n else 0) ∧
      (∀ r : Fin 3,
        Fintype.card {j : Fin (2 * n) //
          address.1 1 (e (Sum.inr j)) = r} =
            if r = 0 then n else if r = 1 then n else 0) := by
  sorry
