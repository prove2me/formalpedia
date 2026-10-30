-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_edge_count_repair_543ac5d4_edge_lower
-- name    : WilliamsonShmoys.planar_drawing_maximal_edge_count_repair_543ac5d4_edge_lower
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:17:43.867175+00:00
-- url     : https://prove2.me/theorems/62010fe3-d448-411d-b7ec-bc189d10c652
-- title:
--   Maximality gives the matching planar edge lower bound
-- statement:
--   If a drawable simple graph on at least three vertices has no strictly larger drawable supergraph on the same vertex type, it has at least $3|V|-6$ edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_edge_count_repair_543ac5d4_edge_lower
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ W : SimpleGraph V,
      U <= W →
      WilliamsonShmoys.HasPlanarDrawingOn W →
      W = U) :
    3 * Fintype.card V <= U.edgeSet.ncard + 6 := by sorry
