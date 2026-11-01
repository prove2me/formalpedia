-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_triangulated_edge_count__p2m_7235810a_9787_44ff_bc97_6b6cda77c472_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_has_triangulated_edge_count__p2m_7235810a_9787_44ff_bc97_6b6cda77c472_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:55:33.261169+00:00
-- url     : https://prove2.me/theorems/d750730e-2711-4e55-8b38-5f4dbc12a87a
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph on the same vertex type has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_has_triangulated_edge_count__p2m_7235810a_9787_44ff_bc97_6b6cda77c472_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : HasPlanarDrawingOn W)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ X : SimpleGraph V, W ≤ X → HasPlanarDrawingOn X → X ≤ W) :
    letI : DecidableRel W.Adj := Classical.decRel W.Adj
    W.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
