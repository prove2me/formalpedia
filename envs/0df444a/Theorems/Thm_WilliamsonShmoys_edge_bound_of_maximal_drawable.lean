-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_of_maximal_drawable
-- name    : WilliamsonShmoys.edge_bound_of_maximal_drawable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:04:14.919438+00:00
-- url     : https://prove2.me/theorems/e79653fb-e24f-47f1-bd3b-207cb378293b
-- title:
--   Edge bound for maximal drawable graphs
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_bound_of_maximal_drawable
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hLmax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by sorry
