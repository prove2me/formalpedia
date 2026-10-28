-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_d8c6ec37_9497_4022_a1c3_e053f306de5e_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_d8c6ec37_9497_4022_a1c3_e053f306de5e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:16:24.335926+00:00
-- url     : https://prove2.me/theorems/6297a968-0143-45e6-995c-58d7175eddc8
-- title:
--   Lower edge bound for an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal simple graph with a crossing-free drawing on at least three vertices has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_d8c6ec37_9497_4022_a1c3_e053f306de5e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  sorry
