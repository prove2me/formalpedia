-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_fa13a70a_f07b_4cf3_b92f_4d7140819b58_a1
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_fa13a70a_f07b_4cf3_b92f_4d7140819b58_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:29:08.351193+00:00
-- url     : https://prove2.me/theorems/f624320d-e63d-47e0-83d6-ecbceca14194
-- title:
--   Planar triangulation completion with exact edge count
-- statement:
--   Every finite drawable simple graph on at least three vertices can be extended on the same vertex set to a drawable graph with exactly 3|V|−6 edges, with no decrease in edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_fa13a70a_f07b_4cf3_b92f_4d7140819b58_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 ∧
      WilliamsonShmoys.HasPlanarDrawingOn N := by sorry
