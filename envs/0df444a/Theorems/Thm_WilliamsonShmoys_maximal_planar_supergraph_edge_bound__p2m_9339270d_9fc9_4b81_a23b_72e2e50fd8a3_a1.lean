-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_bound__p2m_9339270d_9fc9_4b81_a23b_72e2e50fd8a3_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_bound__p2m_9339270d_9fc9_4b81_a23b_72e2e50fd8a3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:34:39.505583+00:00
-- url     : https://prove2.me/theorems/06807de4-e70a-4ffd-9441-1bb5fb02d634
-- title:
--   Edge bound for an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing on at least three vertices has at least 3|V|−6 edges. The argument is to show that maximality rules out disconnected components and nontriangular faces, then apply Euler’s formula to the resulting triangulation. It must establish those topological facts for the given continuous-arc drawing predicate, including the strict vertex and edge-intersection conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_bound__p2m_9339270d_9fc9_4b81_a23b_72e2e50fd8a3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      (∀ u v, K.Adj u v → L.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  sorry
