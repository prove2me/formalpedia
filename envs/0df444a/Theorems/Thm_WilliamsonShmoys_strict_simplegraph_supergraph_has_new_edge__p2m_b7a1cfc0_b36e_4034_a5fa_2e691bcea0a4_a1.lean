-- Prove2me | Theorems.Thm_WilliamsonShmoys_strict_simplegraph_supergraph_has_new_edge__p2m_b7a1cfc0_b36e_4034_a5fa_2e691bcea0a4_a1
-- name    : WilliamsonShmoys.strict_simplegraph_supergraph_has_new_edge__p2m_b7a1cfc0_b36e_4034_a5fa_2e691bcea0a4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:37:29.652572+00:00
-- url     : https://prove2.me/theorems/e818b657-f21b-4dd0-baf1-29be6a66eb68
-- title:
--   Strict simple graph supergraphs add an edge
-- statement:
--   If one simple graph includes another but is not equal to it, then it has an edge absent from the smaller graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.strict_simplegraph_supergraph_has_new_edge__p2m_b7a1cfc0_b36e_4034_a5fa_2e691bcea0a4_a1
    {V : Type} [Fintype V]
    (K L : SimpleGraph V) (hsub : K ≤ L) (hne : L ≠ K) :
    ∃ u v, L.Adj u v ∧ ¬ K.Adj u v := by sorry
