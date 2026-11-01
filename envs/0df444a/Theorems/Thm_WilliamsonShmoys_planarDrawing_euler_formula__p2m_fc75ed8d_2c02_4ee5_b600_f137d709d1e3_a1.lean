-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_euler_formula__p2m_fc75ed8d_2c02_4ee5_b600_f137d709d1e3_a1
-- name    : WilliamsonShmoys.planarDrawing_euler_formula__p2m_fc75ed8d_2c02_4ee5_b600_f137d709d1e3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:52:14.540602+00:00
-- url     : https://prove2.me/theorems/d26cf15f-c3a9-447b-9308-076827a02e42
-- title:
--   Euler formula for a connected planar drawing
-- statement:
--   For a finite connected graph with the supplied crossing-free drawing, there is a natural-number face count satisfying Euler's formula. This removes the Euler-characteristic step from the parent. A proof route is to obtain the cyclic order of incident arcs from the drawing, define face walks using the resulting dart permutation, and prove the Euler characteristic via a spanning tree and cotree. No lower bound on the number of vertices is needed for this statement.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_euler_formula__p2m_fc75ed8d_2c02_4ee5_b600_f137d709d1e3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected) :
    ∃ f : ℕ,
      Fintype.card V + f =
        (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2 := by sorry
