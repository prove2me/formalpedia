-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_euler_formula__p2m_7e15a8d6_7041_4a6f_b660_410e45ab60c6_a1
-- name    : WilliamsonShmoys.planarDrawing_euler_formula__p2m_7e15a8d6_7041_4a6f_b660_410e45ab60c6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:26:57.859344+00:00
-- url     : https://prove2.me/theorems/628f8d78-8c97-48b1-95ad-6d9feb1bca2c
-- title:
--   Euler formula for a connected planar drawing
-- statement:
--   For a finite connected simple graph with a crossing-free drawing, there is a natural number of faces satisfying Euler’s formula, with vertices plus faces equal to edges plus two. The drawing supplies the embedding; connectedness is needed for the stated Euler formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_euler_formula__p2m_7e15a8d6_7041_4a6f_b660_410e45ab60c6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hconn : G.Connected)
    (hG : HasPlanarDrawingOn G) :
    ∃ f : ℕ,
      Fintype.card V + f = (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2 := by sorry
