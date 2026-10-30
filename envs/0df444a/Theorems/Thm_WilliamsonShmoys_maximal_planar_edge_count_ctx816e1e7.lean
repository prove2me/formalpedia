-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_ctx816e1e7
-- name    : WilliamsonShmoys.maximal_planar_edge_count_ctx816e1e7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:51:14.036388+00:00
-- url     : https://prove2.me/theorems/325257b5-4fd9-4dea-bc61-ac16e3a0b2dc
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable simple supergraph has 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_ctx816e1e7
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hmax : ∀ R : SimpleGraph V,
      Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R = Q) :
    Q.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
