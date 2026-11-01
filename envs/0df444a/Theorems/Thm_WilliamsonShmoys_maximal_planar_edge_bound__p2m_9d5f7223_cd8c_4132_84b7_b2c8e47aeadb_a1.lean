-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_9d5f7223_cd8c_4132_84b7_b2c8e47aeadb_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_bound__p2m_9d5f7223_cd8c_4132_84b7_b2c8e47aeadb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:17:54.925542+00:00
-- url     : https://prove2.me/theorems/4762f418-9ea4-4d75-92d4-167b1519faba
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on its vertex set has at least 3|V|−6 edges. This separates the planar-topology and counting work from the parent's finite maximization step. A proof route shows maximality forces the usual triangulation property by inserting an edge in any face that is not triangular, then applies Euler's formula and counts each edge twice across face boundaries. The remaining core is establishing these face and edge-insertion facts from the exact continuous-arc drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound__p2m_9d5f7223_cd8c_4132_84b7_b2c8e47aeadb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
