-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_via_triangulation_a4779231
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_via_triangulation_a4779231
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:58:27.970567+00:00
-- url     : https://prove2.me/theorems/162e488e-8486-418f-9958-cd89573ebf95
-- title:
--   Maximal planar graph edge bound from triangulation
-- statement:
--   A maximal finite simple graph with a crossing-free drawing and at least three vertices has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_via_triangulation_a4779231
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : forall L : SimpleGraph V,
      K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    3 * Fintype.card V - 6 <= K.edgeSet.ncard := by sorry
