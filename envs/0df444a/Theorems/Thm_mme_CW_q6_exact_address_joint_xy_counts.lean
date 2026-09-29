-- Prove2me | Theorems.Thm_mme_CW_q6_exact_address_joint_xy_counts
-- name    : mme_CW_q6_exact_address_joint_xy_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:32:37.395572+00:00
-- url     : https://prove2.me/theorems/6be53637-35a9-4c5c-ba4a-dd41cb2d91a7
-- title:
--   Exact four-cell joint counts in a coupled q=6 address
-- statement:
--   Let an exact coupled q=6 address have length $2N$, supported coordinate types $000,111,012,102$, balanced first and second marginals, and mode-two multiplicities $(L,L,2G)$, where $L+G=N$. Then the four supported joint $(X,Y)$ cells have respective cardinalities
--
--   $$|00|=L; |11|=L; |01|=G; |10|=G.$$
--
--   This exact joint table is the combinatorial input for balanced position reindexing when two cyclic 121/211 source powers are paired into one coupled address.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), the four coupled constituent types and exact profile on pp. 270-271.

import Mathlib.Tactic
import Definitions.Def_mme_CW_q6_primary_hash_family

open MME

set_option autoImplicit false

theorem mme_CW_q6_exact_address_joint_xy_counts
    {N L G : ℕ} (hLG : L + G = N)
    (address : CWQ6ExactCoupledAddress N L G) :
    ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => address.1 0 j = 0 ∧ address.1 1 j = 0)).card = L ∧
    ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => address.1 0 j = 1 ∧ address.1 1 j = 1)).card = L ∧
    ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => address.1 0 j = 0 ∧ address.1 1 j = 1)).card = G ∧
    ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => address.1 0 j = 1 ∧ address.1 1 j = 0)).card = G := by
  sorry
