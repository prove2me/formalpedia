-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_b4696467_bd7a_4833_91a4_199ab5144504_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_b4696467_bd7a_4833_91a4_199ab5144504_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:08:14.581384+00:00
-- url     : https://prove2.me/theorems/77d68189-39bf-4e13-b3a3-9f804ba94476
-- title:
--   Maximal drawable graph edge-count lower bound
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph on the same vertices has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_b4696467_bd7a_4833_91a4_199ab5144504_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L → K ≤ L → K = L)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  sorry
