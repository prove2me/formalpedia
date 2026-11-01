-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_5897f64b_d93f_46d0_b145_4fa00606e1c1_a3
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_5897f64b_d93f_46d0_b145_4fa00606e1c1_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:21:59.905283+00:00
-- url     : https://prove2.me/theorems/6c38f994-ece4-4203-a560-fc77ff979b9c
-- title:
--   Euler edge bound for a planar drawing, including small cases
-- statement:
--   A graph with the specified crossing-free drawing has at most 3n−6 edges when n≥3, and at most n−1 edges when n≤2. The large case follows from Euler's formula, applied to connected components; the small case follows from simplicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_5897f64b_d93f_46d0_b145_4fa00606e1c1_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) :
    (3 ≤ Fintype.card V →
      6 + M.edgeSet.ncard ≤ 3 * Fintype.card V) ∧
    (Fintype.card V ≤ 2 →
      M.edgeSet.ncard ≤ Fintype.card V - 1) := by
  sorry
