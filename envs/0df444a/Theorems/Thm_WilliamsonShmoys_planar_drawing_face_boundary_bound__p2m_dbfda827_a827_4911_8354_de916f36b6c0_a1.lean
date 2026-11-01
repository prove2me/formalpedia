-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_boundary_bound__p2m_dbfda827_a827_4911_8354_de916f36b6c0_a1
-- name    : WilliamsonShmoys.planar_drawing_face_boundary_bound__p2m_dbfda827_a827_4911_8354_de916f36b6c0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:07:35.608246+00:00
-- url     : https://prove2.me/theorems/e44127b7-e307-4dd9-bc34-b67b377ea4eb
-- title:
--   Face boundary incidence bound
-- statement:
--   For this connected simple plane graph, any natural face count satisfying Euler's equation obeys 3f ≤ 2|E|.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.planar_drawing_face_boundary_bound__p2m_dbfda827_a827_4911_8354_de916f36b6c0_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (dK : DecidableRel K.Adj) (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hcard : 3 <= Fintype.card V) : ∀ f : ℕ, Fintype.card V + f = K.edgeFinset.card + 2 → 3 * f <= 2 * K.edgeFinset.card := by sorry
