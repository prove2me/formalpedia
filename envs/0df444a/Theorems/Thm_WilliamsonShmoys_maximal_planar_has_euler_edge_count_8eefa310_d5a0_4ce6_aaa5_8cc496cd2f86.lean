-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_has_euler_edge_count_8eefa310_d5a0_4ce6_aaa5_8cc496cd2f86
-- name    : WilliamsonShmoys.maximal_planar_has_euler_edge_count_8eefa310_d5a0_4ce6_aaa5_8cc496cd2f86
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:13:49.02059+00:00
-- url     : https://prove2.me/theorems/3909e30c-a531-4010-a48d-ad4d6b0818e8
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal under drawable supergraph inclusion has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_has_euler_edge_count_8eefa310_d5a0_4ce6_aaa5_8cc496cd2f86
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hmax : ∀ K : SimpleGraph V,
      J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J) :
    J.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
