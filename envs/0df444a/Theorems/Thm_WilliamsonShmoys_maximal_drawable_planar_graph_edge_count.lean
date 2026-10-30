-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_planar_graph_edge_count
-- name    : WilliamsonShmoys.maximal_drawable_planar_graph_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:49:47.570143+00:00
-- url     : https://prove2.me/theorems/75d9d3d1-0243-482d-89d9-6149ce17f631
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable finite simple graph on at least three vertices that maximizes edge count among drawable supergraphs has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_planar_graph_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L →
      L.edgeSet.ncard ≤ K.edgeSet.ncard) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
