-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_ddfe16f2_466b_4eda_98ed_20e5107df448_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_ddfe16f2_466b_4eda_98ed_20e5107df448_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:25:14.955809+00:00
-- url     : https://prove2.me/theorems/bf52c7e7-38dd-4797-a237-775f0494e419
-- title:
--   Edge count of a maximal drawable planar graph
-- statement:
--   A drawable graph on at least three vertices that has no drawable strict supergraph on the same vertex type has exactly `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_ddfe16f2_466b_4eda_98ed_20e5107df448_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hDraw : HasPlanarDrawingOn T) (hV : 3 ≤ Fintype.card V) (hMax : ∀ N : SimpleGraph V, T ≤ N → HasPlanarDrawingOn N → N ≤ T) : 3 * Fintype.card V = T.edgeSet.ncard + 6 := by sorry
