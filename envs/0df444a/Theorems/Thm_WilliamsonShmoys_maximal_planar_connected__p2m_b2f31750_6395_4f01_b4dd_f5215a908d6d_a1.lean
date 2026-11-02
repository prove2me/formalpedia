-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_connected__p2m_b2f31750_6395_4f01_b4dd_f5215a908d6d_a1
-- name    : WilliamsonShmoys.maximal_planar_connected__p2m_b2f31750_6395_4f01_b4dd_f5215a908d6d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:38:21.2472+00:00
-- url     : https://prove2.me/theorems/5587bd77-cdbe-4d4a-9ac4-bb8e9f059500
-- title:
--   Maximal planar graph is connected
-- statement:
--   A maximal planar graph with at least three vertices is connected. This isolates the step needed to apply the connected form of Euler’s formula. A proof route is to use a planar drawing to connect two distinct components by an arc in a complementary region, then contradict maximality. The vertex lower bound excludes degenerate empty and singleton cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_connected__p2m_b2f31750_6395_4f01_b4dd_f5215a908d6d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    N.Connected := by sorry
