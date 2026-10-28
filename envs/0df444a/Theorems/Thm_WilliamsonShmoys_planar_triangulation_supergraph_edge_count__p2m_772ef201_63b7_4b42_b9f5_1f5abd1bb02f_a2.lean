-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_edge_count__p2m_772ef201_63b7_4b42_b9f5_1f5abd1bb02f_a2
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_edge_count__p2m_772ef201_63b7_4b42_b9f5_1f5abd1bb02f_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:20:36.434043+00:00
-- url     : https://prove2.me/theorems/950f72dd-6d17-4b3b-8f95-2c20bcaaa4d7
-- title:
--   Exact edge count for a planar triangulation extension
-- statement:
--   Every drawable graph on at least three vertices extends on the same vertex set to a drawable graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_supergraph_edge_count__p2m_772ef201_63b7_4b42_b9f5_1f5abd1bb02f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
