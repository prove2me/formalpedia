-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_v2
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_drawing_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:38:55.906569+00:00
-- url     : https://prove2.me/theorems/5ffd9c02-c795-4f45-886d-bb10f1327434
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   An edge-maximal simple graph admitting a crossing-free drawing on at least three vertices has exactly 3|V|−6 edges. The vertex threshold is required; the formula does not hold for maximal planar graphs on fewer than three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_maximal_planar_drawing_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hmax : ∀ R : SimpleGraph V, Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R = Q) :
    3 * Fintype.card V - 6 = Q.edgeSet.ncard := by sorry
