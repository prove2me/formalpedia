-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_0fdafab4_3fd6_4759_8b58_e983a7df1ef3_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_0fdafab4_3fd6_4759_8b58_e983a7df1ef3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T19:20:14.48073+00:00
-- url     : https://prove2.me/theorems/086e0035-b1b1-47b8-9347-227154b90d05
-- title:
--   Edge lower bound for an edge-maximal planar drawing
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable strict edge extension has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_0fdafab4_3fd6_4759_8b58_e983a7df1ef3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet ⊆ L.edgeSet) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
