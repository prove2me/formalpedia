-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_has_exact_edge_count__p2m_aaf33811_225e_424c_a7fa_7688f68b512b_a1
-- name    : WilliamsonShmoys.planar_edge_maximal_has_exact_edge_count__p2m_aaf33811_225e_424c_a7fa_7688f68b512b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:34:13.784543+00:00
-- url     : https://prove2.me/theorems/b1659f81-1f0c-4922-9013-d0dbf115cc22
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strict drawable supergraph on the same vertices has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_maximal_has_exact_edge_count__p2m_aaf33811_225e_424c_a7fa_7688f68b512b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V - 6 = L.edgeSet.ncard := by sorry
