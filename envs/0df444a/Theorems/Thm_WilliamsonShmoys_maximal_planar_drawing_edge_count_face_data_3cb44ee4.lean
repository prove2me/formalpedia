-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_face_data_3cb44ee4
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_face_data_3cb44ee4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T13:41:35.961217+00:00
-- url     : https://prove2.me/theorems/b0c09d1f-62d1-4aeb-b9a9-720dbfe5cf68
-- title:
--   Edge count for maximal planar drawing face data
-- statement:
--   A finite simple graph with a crossing-free drawing that is maximal among drawable supergraphs on the same vertex type has exactly 3|V|−6 edges when it has at least three vertices. This removes the topological edge-count obligation from the parent; it can be proved by showing maximality forces triangular faces and then applying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_face_data_3cb44ee4
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
