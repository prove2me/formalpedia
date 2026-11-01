-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_10381148_6b51_4b84_8aa4_8b409082ba4a_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_count__p2m_10381148_6b51_4b84_8aa4_8b409082ba4a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:20:36.161257+00:00
-- url     : https://prove2.me/theorems/1011a2ca-0dda-4069-a6bc-e4d75ecb3269
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that is inclusion-maximal among drawable supergraphs on those vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count__p2m_10381148_6b51_4b84_8aa4_8b409082ba4a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L = K) :
    3 * Fintype.card V - 6 = K.edgeSet.ncard := by sorry
