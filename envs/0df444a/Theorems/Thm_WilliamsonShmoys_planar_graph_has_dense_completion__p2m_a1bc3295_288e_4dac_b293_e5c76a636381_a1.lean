-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_dense_completion__p2m_a1bc3295_288e_4dac_b293_e5c76a636381_a1
-- name    : WilliamsonShmoys.planar_graph_has_dense_completion__p2m_a1bc3295_288e_4dac_b293_e5c76a636381_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T22:21:54.537774+00:00
-- url     : https://prove2.me/theorems/5479ae8d-caff-4270-918d-e124546166f7
-- title:
--   Dense planar completion
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has a crossing-free supergraph on the same vertices with at least 3|V|−6 edges. The completion is obtained by augmenting the drawing to a triangulation and applying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.planar_graph_has_dense_completion__p2m_a1bc3295_288e_4dac_b293_e5c76a636381_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    ∃ N : SimpleGraph V,
      L <= N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V <= N.edgeSet.ncard + 6 := by sorry
