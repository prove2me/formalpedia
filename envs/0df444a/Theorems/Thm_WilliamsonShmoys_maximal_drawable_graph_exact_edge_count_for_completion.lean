-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_exact_edge_count_for_completion
-- name    : WilliamsonShmoys.maximal_drawable_graph_exact_edge_count_for_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:59:05.463386+00:00
-- url     : https://prove2.me/theorems/6d188ead-74b5-4d1b-b8f4-b13605cf725e
-- title:
--   A maximal drawable graph has the planar triangulation edge count
-- statement:
--   Every inclusion-maximal drawable simple graph on at least three finite vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_exact_edge_count_for_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
