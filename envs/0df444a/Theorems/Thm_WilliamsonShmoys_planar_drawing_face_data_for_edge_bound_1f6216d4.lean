-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data_for_edge_bound_1f6216d4
-- name    : WilliamsonShmoys.planar_drawing_face_data_for_edge_bound_1f6216d4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T02:06:11.895904+00:00
-- url     : https://prove2.me/theorems/954f7585-7fa1-4081-ba59-71da7d8d78f3
-- title:
--   Finite face data from a connected planar drawing
-- statement:
--   The crossing-free drawing of a connected simple graph on at least three vertices yields a finite face count and face-degree function satisfying Euler’s equation, total facial degree 2m, and degree at least three for every face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_data_for_edge_bound_1f6216d4
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ (F : Nat) (degree : Fin F → Nat),
      Fintype.card V + F = H.edgeSet.ncard + 2 ∧
      (∑ f : Fin F, degree f) = 2 * H.edgeSet.ncard ∧
      (∀ f, 3 <= degree f) := by sorry
