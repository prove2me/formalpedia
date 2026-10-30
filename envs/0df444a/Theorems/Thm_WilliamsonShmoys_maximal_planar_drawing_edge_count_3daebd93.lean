-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_3daebd93
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_3daebd93
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:32:35.028607+00:00
-- url     : https://prove2.me/theorems/6a6d07b8-00df-475a-9a7a-0d19bcdc1808
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertex set has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_3daebd93
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → K = L) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
