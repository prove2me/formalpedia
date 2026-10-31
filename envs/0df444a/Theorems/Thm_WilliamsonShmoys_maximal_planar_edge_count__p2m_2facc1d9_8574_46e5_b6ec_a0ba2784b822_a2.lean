-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_2facc1d9_8574_46e5_b6ec_a0ba2784b822_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_2facc1d9_8574_46e5_b6ec_a0ba2784b822_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:25:58.302641+00:00
-- url     : https://prove2.me/theorems/2fb47aec-a2d4-4461-b163-c5191dccad64
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on a finite linearly ordered vertex type with at least three vertices has exactly 3|V|−6 edges. Prove by showing the drawing is connected and every face is triangular, then apply Euler’s formula. The cutoff handles the three-vertex boundary and excludes smaller graphs where the formula fails.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_2facc1d9_8574_46e5_b6ec_a0ba2784b822_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ H : SimpleGraph V, L ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
