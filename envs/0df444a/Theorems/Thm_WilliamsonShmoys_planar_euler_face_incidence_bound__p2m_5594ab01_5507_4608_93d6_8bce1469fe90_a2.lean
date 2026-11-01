-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_euler_face_incidence_bound__p2m_5594ab01_5507_4608_93d6_8bce1469fe90_a2
-- name    : WilliamsonShmoys.planar_euler_face_incidence_bound__p2m_5594ab01_5507_4608_93d6_8bce1469fe90_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:46:16.306758+00:00
-- url     : https://prove2.me/theorems/7c073d05-f8af-49af-8234-528c2585cbfc
-- title:
--   Planar face-incidence bound from Euler’s equation
-- statement:
--   For a connected simply planar-drawn graph with at least three vertices, every natural face count satisfying Euler’s equation obeys the stated incidence bound. A proof route is to count edge incidences in face-boundary walks and establish the corresponding simple planar edge bound, including the case of bridges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_euler_face_incidence_bound__p2m_5594ab01_5507_4608_93d6_8bce1469fe90_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hconn : H.Connected)
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    ∀ f : ℕ,
      Fintype.card V + f = H.edgeFinset.card + 2 →
      3 * f ≤ 2 * H.edgeFinset.card := by sorry
