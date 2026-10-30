-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_euler_edge_count_for_euler_completion
-- name    : WilliamsonShmoys.maximal_planar_graph_euler_edge_count_for_euler_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:50:51.202854+00:00
-- url     : https://prove2.me/theorems/a4779231-70e6-47f0-b9f3-8dd22845a6f3
-- title:
--   Euler edge count for a maximal planar graph
-- statement:
--   A maximal planar simple graph on a finite ordered vertex type with at least three vertices has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_euler_edge_count_for_euler_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : forall L : SimpleGraph V,
      K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
