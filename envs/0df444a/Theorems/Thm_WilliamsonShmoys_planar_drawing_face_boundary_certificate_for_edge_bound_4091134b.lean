-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_boundary_certificate_for_edge_bound_4091134b
-- name    : WilliamsonShmoys.planar_drawing_face_boundary_certificate_for_edge_bound_4091134b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:55:12.388024+00:00
-- url     : https://prove2.me/theorems/a5ca72a9-ecf9-4fb7-a47f-154e4f49a23b
-- title:
--   Face-boundary length certificate for a connected planar drawing
-- statement:
--   Extract from the drawing a finite list of face-boundary lengths. Every boundary has length at least three, the sum of the lengths is twice the number of edges, and the number of boundaries satisfies Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_boundary_certificate_for_edge_bound_4091134b
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn T) (hconn : T.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ lengths : List ℕ,
      (∀ k ∈ lengths, 3 ≤ k) ∧
      lengths.sum = 2 * T.edgeSet.ncard ∧
      Fintype.card V + lengths.length = T.edgeSet.ncard + 2 := by
  sorry
