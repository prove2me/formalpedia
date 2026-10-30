-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_20261026
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:15:52.42931+00:00
-- url     : https://prove2.me/theorems/444ade72-187f-4281-8de5-22015c375f7d
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An edge-maximal simple graph with a crossing-free drawing and at least three vertices has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ J : SimpleGraph V,
      K ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
