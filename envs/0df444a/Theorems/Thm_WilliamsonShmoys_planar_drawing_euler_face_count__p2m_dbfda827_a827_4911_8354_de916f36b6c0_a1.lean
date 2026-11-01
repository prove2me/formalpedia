-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_dbfda827_a827_4911_8354_de916f36b6c0_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_face_count__p2m_dbfda827_a827_4911_8354_de916f36b6c0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:07:34.94313+00:00
-- url     : https://prove2.me/theorems/a918a909-f7d2-4053-adf8-bd862cb1b60d
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   For a finite connected graph with the supplied crossing-free drawing, Euler's formula gives a natural number of faces f with |V| + f = |E| + 2.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.planar_drawing_euler_face_count__p2m_dbfda827_a827_4911_8354_de916f36b6c0_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (dK : DecidableRel K.Adj) (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hcard : 3 <= Fintype.card V) : ∃ f : ℕ, Fintype.card V + f = K.edgeFinset.card + 2 := by sorry
