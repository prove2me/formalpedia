-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula__p2m_89410822_d74b_4a7e_a2
-- name    : WilliamsonShmoys.planar_drawing_euler_formula__p2m_89410822_d74b_4a7e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:12:45.379887+00:00
-- url     : https://prove2.me/theorems/6b10014f-77c9-4b92-a047-aa6e2b76d351
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   Every finite connected graph with a crossing-free drawing on the plane has a natural-number face count satisfying Euler's formula, with no lower bound on the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_formula__p2m_89410822_d74b_4a7e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected) :
    ∃ f : ℕ,
      Fintype.card V + f =
        (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2 := by sorry
