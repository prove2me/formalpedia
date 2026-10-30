-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_4e1da140_2dc1_48aa_a5de_903746e6acda_a7
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_4e1da140_2dc1_48aa_a5de_903746e6acda_a7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T04:03:55.261396+00:00
-- url     : https://prove2.me/theorems/accf786d-4436-4249-b439-8ab55fe05a76
-- title:
--   Maximal planar graph edge-count lower bound
-- statement:
--   An inclusion-maximal graph with the supplied planar drawing and at least three vertices has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Tactic
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_4e1da140_2dc1_48aa_a5de_903746e6acda_a7
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hLmax : forall M : SimpleGraph V,
      L.edgeSet <= M.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      M.edgeSet <= L.edgeSet) :
    3 * Fintype.card V <= L.edgeSet.ncard + 6 := by sorry
