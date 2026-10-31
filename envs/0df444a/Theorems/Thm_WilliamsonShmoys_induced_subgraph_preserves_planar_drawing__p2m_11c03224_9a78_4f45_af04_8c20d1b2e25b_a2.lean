-- Prove2me | Theorems.Thm_WilliamsonShmoys_induced_subgraph_preserves_planar_drawing__p2m_11c03224_9a78_4f45_af04_8c20d1b2e25b_a2
-- name    : WilliamsonShmoys.induced_subgraph_preserves_planar_drawing__p2m_11c03224_9a78_4f45_af04_8c20d1b2e25b_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:35:00.44741+00:00
-- url     : https://prove2.me/theorems/2a50bc8a-1aee-413c-8544-35b101dc4879
-- title:
--   Restricting a planar drawing to an induced subgraph
-- statement:
--   Restricting the vertices and edges of a graph with a crossing-free drawing to a finite vertex subset preserves the drawing property. This packages the direct restriction of the point and arc maps along subtype coercion; no additional size or connectivity hypotheses are needed. A proof route is to unpack HasPlanarDrawingOn, compose its point and arc maps with the subtype coercion, and discharge the drawing conditions using induced adjacency and the inherited linear order.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.induced_subgraph_preserves_planar_drawing__p2m_11c03224_9a78_4f45_af04_8c20d1b2e25b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (s : Finset V) :
    HasPlanarDrawingOn (L.induce (s : Set V)) := by sorry
