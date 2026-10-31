-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_face_count_data
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_for_face_count_data
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:31:53.604538+00:00
-- url     : https://prove2.me/theorems/2deee9ab-c8c5-41fd-b97d-2bfa82fc7018
-- title:
--   Edge count of a maximal planar drawing for face-count data
-- statement:
--   A crossing-free drawable simple graph on at least three vertices that has no drawable simple-graph extension on the same vertex set has exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarFaceCountData

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_for_face_count_data
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
