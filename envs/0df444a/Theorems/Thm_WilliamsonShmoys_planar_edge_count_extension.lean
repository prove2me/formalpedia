-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_extension
-- name    : WilliamsonShmoys.planar_edge_count_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:03:36.623376+00:00
-- url     : https://prove2.me/theorems/8e5811e7-c4f9-482d-b149-bd96024e3b10
-- title:
--   Drawable graphs admit a planar supergraph with the maximal planar edge count
-- statement:
--   Every graph with a crossing-free drawing on a finite linearly ordered vertex type of size at least three has a drawable supergraph on the same vertex type with exactly `3 * card V - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        3 * Fintype.card V = H.edgeSet.ncard + 6 := by sorry
