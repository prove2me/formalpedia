-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_count_inequality_of_drawing
-- name    : WilliamsonShmoys.planar_face_count_inequality_of_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:24:24.041993+00:00
-- url     : https://prove2.me/theorems/7379e96c-5645-4e15-b04d-78d4884cf4e2
-- title:
--   Euler face count and boundary length for a connected simple planar drawing
-- statement:
--   For a connected simple graph with at least three vertices and a crossing-free drawing, there is a natural number of faces satisfying Euler’s formula, and the sum of face-boundary lengths is at least three per face and equals twice the number of edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_face_count_inequality_of_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : L.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * L.edgeSet.ncard := by sorry
