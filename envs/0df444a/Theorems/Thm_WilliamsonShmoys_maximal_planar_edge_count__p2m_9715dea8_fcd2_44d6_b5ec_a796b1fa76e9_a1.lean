-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_9715dea8_fcd2_44d6_b5ec_a796b1fa76e9_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_9715dea8_fcd2_44d6_b5ec_a796b1fa76e9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:44:49.03754+00:00
-- url     : https://prove2.me/theorems/b8a812cb-4c6a-4971-bdf9-7db1f5ebc92f
-- title:
--   Count the edges of a maximal drawable graph
-- statement:
--   An inclusion maximal drawable simple graph on at least three vertices has exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_9715dea8_fcd2_44d6_b5ec_a796b1fa76e9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
