-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_accounting
-- name    : WilliamsonShmoys.planar_drawing_face_accounting
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:59:55.835999+00:00
-- url     : https://prove2.me/theorems/57972424-e6b5-450b-8797-923265814c99
-- title:
--   Euler and boundary accounting for a connected plane drawing
-- statement:
--   A finite connected simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn admits a face count f and total facial boundary length b satisfying Euler’s equation, two incidences per edge, and a minimum of three incidences per face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_face_accounting
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ (f b : Nat),
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      2 * G.edgeSet.ncard = b ∧
      3 * f ≤ b := by sorry
