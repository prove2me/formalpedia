-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_triangulation_edge_count
-- name    : WilliamsonShmoys.maximal_drawable_graph_triangulation_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T10:08:04.126307+00:00
-- url     : https://prove2.me/theorems/89bec016-fb57-45ef-a368-8eccc50472fa
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three finite vertices that is maximal among drawable supergraphs on those vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_triangulation_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
