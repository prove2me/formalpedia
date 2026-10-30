-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_data
-- name    : WilliamsonShmoys.planar_drawing_face_count_data
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:01:50.849996+00:00
-- url     : https://prove2.me/theorems/90183013-31a5-4110-96f4-66fe6684e6d5
-- title:
--   Euler face-count data for a connected planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has a natural-number face count satisfying Euler’s formula, and its total facial boundary length is at least three times the number of faces. The two sides of each edge contribute to the total boundary length.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_count_data
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f <= 2 * G.edgeSet.ncard := by sorry
