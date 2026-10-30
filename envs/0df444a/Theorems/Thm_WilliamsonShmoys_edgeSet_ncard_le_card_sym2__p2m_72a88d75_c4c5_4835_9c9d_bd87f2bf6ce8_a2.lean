-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_le_card_sym2__p2m_72a88d75_c4c5_4835_9c9d_bd87f2bf6ce8_a2
-- name    : WilliamsonShmoys.edgeSet_ncard_le_card_sym2__p2m_72a88d75_c4c5_4835_9c9d_bd87f2bf6ce8_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:26:51.438064+00:00
-- url     : https://prove2.me/theorems/68faed71-4d8b-46d4-abe0-830c78d2f0c8
-- title:
--   A graph's edge count is bounded by its possible pairs
-- statement:
--   For a finite vertex type, a graph’s edge count is at most the number of possible unordered vertex pairs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_le_card_sym2__p2m_72a88d75_c4c5_4835_9c9d_bd87f2bf6ce8_a2
    {V : Type} [Fintype V] (G : SimpleGraph V) :
    G.edgeSet.ncard ≤ Fintype.card (Sym2 V) := by
  sorry
