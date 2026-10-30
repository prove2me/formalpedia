-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_bounds
-- name    : WilliamsonShmoys.planar_drawing_face_count_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:55:37.209953+00:00
-- url     : https://prove2.me/theorems/a4b438ed-e3ef-4372-8d7a-a9cc6a64462c
-- title:
--   Euler face count and boundary bound for a planar drawing
-- statement:
--   A connected simple graph with at least three vertices and the specified crossing-free drawing has a finite face count satisfying Euler’s formula, and its total facial boundary length gives three times the number of faces at most twice the number of edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_count_bounds
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 <= Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by sorry
