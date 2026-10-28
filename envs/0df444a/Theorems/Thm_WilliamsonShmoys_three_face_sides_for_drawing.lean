-- Prove2me | Theorems.Thm_WilliamsonShmoys_three_face_sides_for_drawing
-- name    : WilliamsonShmoys.three_face_sides_for_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:39:53.10484+00:00
-- url     : https://prove2.me/theorems/ea237986-dde8-45aa-8717-82b33fafcc6c
-- title:
--   At least three edge-sides per face
-- statement:
--   For a connected simple graph on at least three vertices with a planar drawing and an Euler face count f, the total face boundary length is at least three per face and equals twice the number of edges, counting a bridge twice.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.three_face_sides_for_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 <= Fintype.card V)
    (f : Nat)
    (hEuler : Fintype.card V + f = G.edgeSet.ncard + 2) :
    3 * f <= 2 * G.edgeSet.ncard := by sorry
