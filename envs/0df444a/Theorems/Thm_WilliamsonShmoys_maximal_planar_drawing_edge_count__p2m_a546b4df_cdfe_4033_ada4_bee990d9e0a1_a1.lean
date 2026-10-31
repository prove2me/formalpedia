-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_a546b4df_cdfe_4033_ada4_bee990d9e0a1_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_a546b4df_cdfe_4033_ada4_bee990d9e0a1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:55:47.009995+00:00
-- url     : https://prove2.me/theorems/50304f69-3f87-43f6-91bb-4f1f44440925
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph on the same vertex set has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_a546b4df_cdfe_4033_ada4_bee990d9e0a1_a1 {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hDraw : HasPlanarDrawingOn S) (hV : 3 <= Fintype.card V) (hMax : ∀ T : SimpleGraph V, S ≤ T → HasPlanarDrawingOn T → T = S) : S.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
