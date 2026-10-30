-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_79011c86fe2a4d17
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_79011c86fe2a4d17
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:04:33.605579+00:00
-- url     : https://prove2.me/theorems/0e6cbe52-e2e3-41cf-80dc-2d34dacc7938
-- title:
--   Edge lower bound for maximal drawable graphs
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite ordered vertices has at least three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_79011c86fe2a4d17
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ W : SimpleGraph V, U ≤ W →
      WilliamsonShmoys.HasPlanarDrawingOn W → W = U) :
    3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := by sorry
