-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_add_edge_below_max
-- name    : WilliamsonShmoys.planar_graph_add_edge_below_max
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T20:23:11.764775+00:00
-- url     : https://prove2.me/theorems/c58be912-27e8-4387-96f7-ac1f50cf37d2
-- title:
--   A drawable graph below the triangulation count admits an edge augmentation
-- statement:
--   If a drawable simple graph on at least three vertices has fewer than 3|V|−6 edges, it has a strict drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_add_edge_below_max
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hSmall : R.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ S : SimpleGraph V, R < S ∧ WilliamsonShmoys.HasPlanarDrawingOn S := by sorry
