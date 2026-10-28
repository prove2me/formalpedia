-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_bound
-- name    : WilliamsonShmoys.planar_drawing_face_count_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:08:52.984915+00:00
-- url     : https://prove2.me/theorems/4a97232d-5b22-4cc7-8cd0-c0312d11cb0d
-- title:
--   Euler face count and boundary length for a connected planar drawing
-- statement:
--   A connected simple graph with at least three vertices and the supplied crossing-free drawing has a finite face count satisfying Euler’s formula and the total face-boundary lower bound. Prove this by constructing the embedding’s faces from the drawing, establishing Euler’s formula, and counting edge sides; simplicity and the vertex lower bound rule out boundary walks too short for the perimeter inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_count_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by sorry
