-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_euler_face_count
-- name    : WilliamsonShmoys.planar_drawing_has_euler_face_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:42:17.114658+00:00
-- url     : https://prove2.me/theorems/917ba23c-4a75-45b2-969b-95b269c17ada
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and a drawing satisfying the supplied crossing-free arc conditions, there is a natural number of faces f such that Euler’s formula holds and the total face-boundary count gives three times the number of faces at most twice the number of edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_euler_face_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hConnected : G.Connected)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, G.edgeSet.ncard + 2 = Fintype.card V + f ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by sorry
