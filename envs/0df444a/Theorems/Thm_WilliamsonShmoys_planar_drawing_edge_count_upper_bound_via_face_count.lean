-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_via_face_count
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound_via_face_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T15:16:29.857168+00:00
-- url     : https://prove2.me/theorems/2c262075-af7a-40b5-8216-f56b847d81a6
-- title:
--   Edge upper bound for a finite simple planar drawing
-- statement:
--   Every finite simple graph on at least three vertices with a drawing satisfying the supplied crossing-free arc predicate has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound_via_face_count {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) : T.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
