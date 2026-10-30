-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_certificate__p2m_cfd012c7_8a6d_483e_9797_29a733a7d0a7_a1
-- name    : WilliamsonShmoys.planar_drawing_face_count_certificate__p2m_cfd012c7_8a6d_483e_9797_29a733a7d0a7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:32:45.325785+00:00
-- url     : https://prove2.me/theorems/a9940316-9fb7-49d9-9418-23da2bfccc13
-- title:
--   Planar drawing face-count certificate
-- statement:
--   For a connected graph with at least three vertices and a crossing-free drawing, there is an integer face count satisfying Euler’s formula and the lower bound on total face-boundary incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_face_count_certificate__p2m_cfd012c7_8a6d_483e_9797_29a733a7d0a7_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hconn : T.Connected) : ∃ f : ℤ, (Fintype.card V : ℤ) - (T.edgeSet.ncard : ℤ) + f = 2 ∧ 3 * f ≤ 2 * (T.edgeSet.ncard : ℤ) := by sorry
