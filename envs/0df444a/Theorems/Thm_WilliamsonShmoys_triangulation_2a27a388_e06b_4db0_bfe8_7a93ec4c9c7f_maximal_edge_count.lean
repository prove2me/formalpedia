-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_maximal_edge_count
-- name    : WilliamsonShmoys.triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_maximal_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T19:08:53.867483+00:00
-- url     : https://prove2.me/theorems/ad65a44e-4192-4c4a-92f5-b78b9563f5a1
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing on at least three vertices has exactly three times the number of vertices minus six edges. This removes the topological and Euler-counting work from the parent. A proof route is to use the drawing arcs as a plane embedding, show maximality rules out disconnected components and nontriangular faces by adding an edge inside a face, and then combine Euler’s formula with the fact that each triangular face contributes three edge incidences and each edge borders two face sides. The lower bound on the number of vertices is essential: on fewer vertices, maximal drawable graphs need not have this edge count. Formalizing this plane-embedding argument from the supplied arc predicate remains the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_maximal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
