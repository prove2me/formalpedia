-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_has_exact_edge_count
-- name    : WilliamsonShmoys.maximal_planar_has_exact_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T04:37:53.946754+00:00
-- url     : https://prove2.me/theorems/f2d3ad88-ed48-4673-937e-a97626de3ff1
-- title:
--   Exact edge count of a maximal drawable graph
-- statement:
--   A drawable finite simple graph with at least three vertices that is maximal among drawable supergraphs on the same vertex type has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_has_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
