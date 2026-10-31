-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq_from_drawing__p2m_cf5b9138_9b5a_4508_a5f4_a698107874c7_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_eq_from_drawing__p2m_cf5b9138_9b5a_4508_a5f4_a698107874c7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:24:18.749039+00:00
-- url     : https://prove2.me/theorems/b89122c2-2828-407e-ad92-2701689cab61
-- title:
--   Exact edge count for maximal planar drawings
-- statement:
--   A finite simple graph with at least three vertices that has a crossing-free drawing and is maximal among planar supergraphs on the same vertex set has exactly 3n−6 edges. The connectedness hypothesis is unnecessary.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_eq_from_drawing__p2m_cf5b9138_9b5a_4508_a5f4_a698107874c7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
