-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_abdda8c5_f5c1_4e5d_b801_c7084d469782_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_abdda8c5_f5c1_4e5d_b801_c7084d469782_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:31:21.613958+00:00
-- url     : https://prove2.me/theorems/7b40ef00-72b0-4fde-a3cb-cf2325177ae8
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   A drawable graph maximal among drawable supergraphs on the same vertex type has at least 3n − 6 edges when n ≥ 3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_abdda8c5_f5c1_4e5d_b801_c7084d469782_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
