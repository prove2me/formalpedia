-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_completion_for_maximal_face_equations_maximal_edge_count
-- name    : WilliamsonShmoys.planar_drawing_edge_count_completion_for_maximal_face_equations_maximal_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T03:54:43.989872+00:00
-- url     : https://prove2.me/theorems/49ccbab8-e6de-4b0b-a4f2-7d457d8bcd5b
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   A drawable finite simple graph on at least three vertices that has no strictly larger drawable supergraph has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_count_completion_for_maximal_face_equations_maximal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
