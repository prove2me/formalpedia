-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_count__p2m_5d494874_3848_4892_940c_cf6b084398e7_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_count__p2m_5d494874_3848_4892_940c_cf6b084398e7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:12:10.953027+00:00
-- url     : https://prove2.me/theorems/a78a6ebd-f14e-4d5e-887a-7bf11c56fcc6
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A connected graph with a drawing satisfying `HasPlanarDrawingOn` has a natural face count satisfying Euler’s formula. This isolates the topological Euler-count step from the later inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_count__p2m_5d494874_3848_4892_940c_cf6b084398e7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeFinset.card + 2 := by sorry
