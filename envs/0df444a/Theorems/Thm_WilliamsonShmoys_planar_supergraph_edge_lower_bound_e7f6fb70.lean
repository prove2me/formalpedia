-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_lower_bound_e7f6fb70
-- name    : WilliamsonShmoys.planar_supergraph_edge_lower_bound_e7f6fb70
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T18:49:19.62464+00:00
-- url     : https://prove2.me/theorems/39dd1b17-555e-42ce-8588-436026f0fe7e
-- title:
--   Drawable graphs have dense drawable supergraphs
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on that same vertex set whose edge count is at least `3n - 6`. Augmenting the embedding to a maximal planar graph and applying Euler’s formula gives the bound. The parent theorem’s maximality hypothesis forces this supergraph to equal the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_edge_lower_bound_e7f6fb70
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    exists Z : SimpleGraph V,
      Y <= Z /\ WilliamsonShmoys.HasPlanarDrawingOn Z /\
        3 * Fintype.card V <= Z.edgeSet.ncard + 6 := by sorry
