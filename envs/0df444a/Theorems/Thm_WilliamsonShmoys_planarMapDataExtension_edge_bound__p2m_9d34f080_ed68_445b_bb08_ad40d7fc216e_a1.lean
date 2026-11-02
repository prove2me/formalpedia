-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarMapDataExtension_edge_bound__p2m_9d34f080_ed68_445b_bb08_ad40d7fc216e_a1
-- name    : WilliamsonShmoys.planarMapDataExtension_edge_bound__p2m_9d34f080_ed68_445b_bb08_ad40d7fc216e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:44:18.227951+00:00
-- url     : https://prove2.me/theorems/5ad44f91-c48a-45cf-8213-5949f49db35c
-- title:
--   Transfer the finite face data edge bound to a subgraph
-- statement:
--   If a finite graph is an edge subgraph of a graph carrying the supplied face data, then with at least three vertices its edge count satisfies the planar bound. Sum the face-degree lower bounds and combine them with the Euler equation to bound the extension’s edges; edge inclusion transfers that bound to the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
import Mathlib

theorem WilliamsonShmoys.planarMapDataExtension_edge_bound__p2m_9d34f080_ed68_445b_bb08_ad40d7fc216e_a1
    {V : Type} [Fintype V]
    (J K : SimpleGraph V) [DecidableRel J.Adj] [DecidableRel K.Adj]
    (hcard : 3 <= Fintype.card V)
    (hsub : ∀ ⦃u v : V⦄, J.Adj u v → K.Adj u v)
    (hdata : Nonempty (PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3 K)) :
    J.edgeFinset.card + 6 <= 3 * Fintype.card V := by sorry
