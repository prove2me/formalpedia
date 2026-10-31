-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_count__p2m_ba617e25_272f_480b_8c9f_e5a82d8e4502_a1
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_edge_count__p2m_ba617e25_272f_480b_8c9f_e5a82d8e4502_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:33:34.598318+00:00
-- url     : https://prove2.me/theorems/9b9fadfe-20c3-484e-b25c-37db0802734a
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three finite vertices that has no proper drawable supergraph on the same vertex set has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_supergraph_edge_count__p2m_ba617e25_272f_480b_8c9f_e5a82d8e4502_a1 {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hS : WilliamsonShmoys.HasPlanarDrawingOn S) (hCard : 3 ≤ Fintype.card V) (hMax : ∀ T : SimpleGraph V, S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S) : S.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
