-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_edge_count__p2m_9011127c_6876_47eb_ac9e_306fd8c6abcc_a2
-- name    : WilliamsonShmoys.maximal_planar_euler_edge_count__p2m_9011127c_6876_47eb_ac9e_306fd8c6abcc_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T09:47:19.501832+00:00
-- url     : https://prove2.me/theorems/5de67bd5-1b50-462c-9c5e-b0f0f644e7f0
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph that is maximal under drawable edge-set extension, on at least three vertices, has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_euler_edge_count__p2m_9011127c_6876_47eb_ac9e_306fd8c6abcc_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ (Set.univ : Set V).ncard)
    (hMax : ∀ P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P →
      N.edgeSet ⊆ P.edgeSet → P.edgeSet ⊆ N.edgeSet) :
    N.edgeSet.ncard + 6 = 3 * (Set.univ : Set V).ncard := by sorry
