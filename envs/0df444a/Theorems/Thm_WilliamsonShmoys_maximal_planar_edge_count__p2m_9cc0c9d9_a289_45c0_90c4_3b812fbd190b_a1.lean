-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_9cc0c9d9_a289_45c0_90c4_3b812fbd190b_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_9cc0c9d9_a289_45c0_90c4_3b812fbd190b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T18:53:21.315223+00:00
-- url     : https://prove2.me/theorems/42a68497-1fb0-460d-90d9-a7891ca5f267
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_9cc0c9d9_a289_45c0_90c4_3b812fbd190b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      Set.Subset M.edgeSet N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  sorry
