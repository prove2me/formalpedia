-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_4c675a48_b2e7_41d9_8987_0c6f38bd3a34_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4c675a48_b2e7_41d9_8987_0c6f38bd3a34_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:40:48.085541+00:00
-- url     : https://prove2.me/theorems/43a07344-7f08-4c1d-acca-1e4a761282d7
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three finite vertices that is maximal under drawable edge extensions has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4c675a48_b2e7_41d9_8987_0c6f38bd3a34_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
