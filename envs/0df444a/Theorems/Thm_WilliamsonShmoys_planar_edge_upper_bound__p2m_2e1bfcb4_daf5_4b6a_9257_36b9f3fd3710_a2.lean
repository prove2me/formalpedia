-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_2e1bfcb4_daf5_4b6a_9257_36b9f3fd3710_a2
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_2e1bfcb4_daf5_4b6a_9257_36b9f3fd3710_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:38:34.23466+00:00
-- url     : https://prove2.me/theorems/2b671f0d-81a7-40a8-b867-3baa78ac7677
-- title:
--   Simple planar graphs satisfy the Euler edge bound
-- statement:
--   A simple graph with a crossing-free drawing and at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_2e1bfcb4_daf5_4b6a_9257_36b9f3fd3710_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
