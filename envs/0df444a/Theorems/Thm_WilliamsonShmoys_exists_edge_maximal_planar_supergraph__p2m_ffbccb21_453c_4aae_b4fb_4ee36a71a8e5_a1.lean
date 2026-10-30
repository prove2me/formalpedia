-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_ffbccb21_453c_4aae_b4fb_4ee36a71a8e5_a1
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_ffbccb21_453c_4aae_b4fb_4ee36a71a8e5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:55:44.764995+00:00
-- url     : https://prove2.me/theorems/bea38117-d38f-456c-ab97-6aa292e9c123
-- title:
--   Existence of an edge-maximal planar supergraph
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertices that is maximal under planar edge-preserving extension, and whose edge count is at least that of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_ffbccb21_453c_4aae_b4fb_4ee36a71a8e5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hDraw : HasPlanarDrawingOn N) :
    ∃ H : SimpleGraph V,
      N ≤ H ∧ HasPlanarDrawingOn H ∧
      N.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) := by sorry
