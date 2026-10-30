-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximum_edge_planar_graph_has_euler_edge_count
-- name    : WilliamsonShmoys.maximum_edge_planar_graph_has_euler_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:17:05.981458+00:00
-- url     : https://prove2.me/theorems/f686dd19-dc5b-40c4-8ff2-c304059b5a3b
-- title:
--   Edge count of a maximum-edge drawable graph
-- statement:
--   A drawable simple graph on at least three finite vertices whose edge count is at least that of every drawable supergraph on those vertices has exactly 3|V|−6 edges. The maximum-edge hypothesis rules out any strict drawable supergraph, after which maximal-planar structure and Euler’s formula give the count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximum_edge_planar_graph_has_euler_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ N.edgeSet.ncard) :
    3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  sorry
