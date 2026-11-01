-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_25a042c7_1a1b_47c9_a392_cae86f15b395_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_25a042c7_1a1b_47c9_a392_cae86f15b395_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:22:13.337446+00:00
-- url     : https://prove2.me/theorems/a82d4d7c-d6e6-4425-a735-0c3a8fa81594
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A simple planar graph on at least three vertices that is maximal under inclusion among planar supergraphs on the same vertices has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_25a042c7_1a1b_47c9_a392_cae86f15b395_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
