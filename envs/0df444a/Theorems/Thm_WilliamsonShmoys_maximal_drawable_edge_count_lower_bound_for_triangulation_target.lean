-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound_for_triangulation_target
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_lower_bound_for_triangulation_target
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:21:54.536653+00:00
-- url     : https://prove2.me/theorems/8f32d902-7718-40eb-87e2-098365566fba
-- title:
--   Edge count lower bound for a maximal drawable graph
-- statement:
--   A finite drawable graph maximal among drawable supergraphs, with at least three vertices, has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_lower_bound_for_triangulation_target
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ L : SimpleGraph V, M ≤ L → HasPlanarDrawingOn L → L ≤ M)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by sorry
