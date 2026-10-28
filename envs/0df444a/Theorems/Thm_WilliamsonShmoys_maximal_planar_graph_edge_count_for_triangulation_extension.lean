-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_for_triangulation_extension
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_for_triangulation_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T21:12:00.096067+00:00
-- url     : https://prove2.me/theorems/bf5337c4-e5c1-468b-8112-affc4a404ace
-- title:
--   Edge count of a maximal planar graph for the triangulation extension
-- statement:
--   A drawable graph on at least three finite vertices that has no strictly larger drawable supergraph on those vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_for_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
