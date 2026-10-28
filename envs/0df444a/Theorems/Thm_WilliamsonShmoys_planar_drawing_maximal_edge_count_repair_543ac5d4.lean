-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_edge_count_repair_543ac5d4
-- name    : WilliamsonShmoys.planar_drawing_maximal_edge_count_repair_543ac5d4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T06:06:50.539809+00:00
-- url     : https://prove2.me/theorems/3aad0407-8baf-4dd2-8df6-3afd46b71d5c
-- title:
--   Edge count of a maximal drawable graph for the repair
-- statement:
--   A drawable simple graph on at least three vertices that admits no strictly larger drawable supergraph on the same vertex type has exactly $3|V|-6$ edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_edge_count_repair_543ac5d4
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ W : SimpleGraph V,
      U <= W →
      WilliamsonShmoys.HasPlanarDrawingOn W →
      W = U) :
    3 * Fintype.card V = U.edgeSet.ncard + 6 := by sorry
