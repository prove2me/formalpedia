-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph_for_edge_bound_v2
-- name    : WilliamsonShmoys.exists_triangulated_planar_supergraph_for_edge_bound_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:20:12.236878+00:00
-- url     : https://prove2.me/theorems/89a3906c-715e-4b0e-a30b-90b3a1c82cb7
-- title:
--   Planar augmentation to the edge bound
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is contained in a drawable simple graph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_triangulated_planar_supergraph_for_edge_bound_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧
        Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
