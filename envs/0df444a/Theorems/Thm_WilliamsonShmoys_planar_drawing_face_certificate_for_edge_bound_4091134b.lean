-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_certificate_for_edge_bound_4091134b
-- name    : WilliamsonShmoys.planar_drawing_face_certificate_for_edge_bound_4091134b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:35:57.425971+00:00
-- url     : https://prove2.me/theorems/b3a89443-f3a4-4e4f-a3b2-62b9b38f66cf
-- title:
--   Face count from a connected planar drawing for the edge bound
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing has a natural-number face count satisfying Euler’s formula and the face-incidence inequality needed for the planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_certificate_for_edge_bound_4091134b
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn T) (hconn : T.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = T.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * T.edgeSet.ncard := by
  sorry
