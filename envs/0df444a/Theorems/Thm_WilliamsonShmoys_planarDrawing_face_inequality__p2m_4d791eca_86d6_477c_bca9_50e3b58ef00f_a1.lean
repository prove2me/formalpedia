-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_face_inequality__p2m_4d791eca_86d6_477c_bca9_50e3b58ef00f_a1
-- name    : WilliamsonShmoys.planarDrawing_face_inequality__p2m_4d791eca_86d6_477c_bca9_50e3b58ef00f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:22:35.732307+00:00
-- url     : https://prove2.me/theorems/7e15a8d6-7041-4a6f-b660-410e45ab60c6
-- title:
--   Euler face-count inequality for connected planar drawings
-- statement:
--   For a connected simple graph on at least three vertices with a crossing-free drawing, there is a natural number of faces such that vertices plus faces equal edges plus two, and the total face-boundary length is at least three per face, with each edge counted twice.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_face_inequality__p2m_4d791eca_86d6_477c_bca9_50e3b58ef00f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hconn : G.Connected)
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2 ∧
        3 * f ≤ 2 * (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) := by sorry
