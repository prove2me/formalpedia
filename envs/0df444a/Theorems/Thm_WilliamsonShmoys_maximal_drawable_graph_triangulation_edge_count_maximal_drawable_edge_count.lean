-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_triangulation_edge_count_maximal_drawable_edge_count
-- name    : WilliamsonShmoys.maximal_drawable_graph_triangulation_edge_count_maximal_drawable_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T10:53:42.363879+00:00
-- url     : https://prove2.me/theorems/f30e0da3-b4e3-4cc1-92aa-c786ff471b76
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_triangulation_edge_count_maximal_drawable_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
