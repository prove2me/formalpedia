-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count_e8dca3ed
-- name    : WilliamsonShmoys.planar_drawing_euler_face_count_e8dca3ed
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T08:07:33.078136+00:00
-- url     : https://prove2.me/theorems/d1d3ed65-54c6-4d93-a9bc-bc821d86856a
-- title:
--   Euler face count and side bound for a crossing-free drawing
-- statement:
--   A connected simple graph on at least three vertices with the specified crossing-free drawing has a finite face count satisfying Euler’s formula and the bound that at least three edge-sides occur per face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_face_count_e8dca3ed
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : G.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by sorry
