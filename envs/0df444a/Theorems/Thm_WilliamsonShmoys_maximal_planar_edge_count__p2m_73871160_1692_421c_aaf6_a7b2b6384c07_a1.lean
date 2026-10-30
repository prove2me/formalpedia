-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_73871160_1692_421c_aaf6_a7b2b6384c07_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_73871160_1692_421c_aaf6_a7b2b6384c07_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T01:03:33.851919+00:00
-- url     : https://prove2.me/theorems/5db777ea-26b2-4b9c-844f-64ae8eedcb74
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A finite drawable simple graph with at least three vertices that is maximal among drawable supergraphs on the same vertex type has exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_73871160_1692_421c_aaf6_a7b2b6384c07_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hmax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ T) (hV : 3 ≤ Fintype.card V) : T.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
