-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_5de67bd5_1b50_462c_9c5e_b0f0f644e7f0_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_5de67bd5_1b50_462c_9c5e_b0f0f644e7f0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T10:03:19.362793+00:00
-- url     : https://prove2.me/theorems/6fee8394-5cd3-41ed-a313-0532b2d14cd3
-- title:
--   Maximal drawable graphs meet the planar edge bound
-- statement:
--   A drawable simple graph on at least three vertices that admits no strict drawable edge-set extension has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_5de67bd5_1b50_462c_9c5e_b0f0f644e7f0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ (Set.univ : Set V).ncard)
    (hMax : ∀ P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P →
      N.edgeSet ⊆ P.edgeSet → P.edgeSet ⊆ N.edgeSet) :
    3 * (Set.univ : Set V).ncard ≤ N.edgeSet.ncard + 6 := by sorry
