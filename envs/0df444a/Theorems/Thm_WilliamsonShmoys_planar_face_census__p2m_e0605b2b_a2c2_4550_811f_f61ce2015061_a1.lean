-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_census__p2m_e0605b2b_a2c2_4550_811f_f61ce2015061_a1
-- name    : WilliamsonShmoys.planar_face_census__p2m_e0605b2b_a2c2_4550_811f_f61ce2015061_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:58:47.596671+00:00
-- url     : https://prove2.me/theorems/2343a1b4-cbe5-4a48-b836-711e4285cb1c
-- title:
--   Euler face census for a connected simple planar graph
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing has a face count satisfying Euler’s formula, and its total face-boundary incidence count is at least three per face and equals twice its edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_face_census__p2m_e0605b2b_a2c2_4550_811f_f61ce2015061_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f <= 2 * H.edgeSet.ncard := by sorry
