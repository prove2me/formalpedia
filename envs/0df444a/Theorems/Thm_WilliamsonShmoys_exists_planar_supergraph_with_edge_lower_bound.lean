-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_edge_lower_bound
-- name    : WilliamsonShmoys.exists_planar_supergraph_with_edge_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:52:50.476078+00:00
-- url     : https://prove2.me/theorems/1b538d07-0bfb-4a9f-87ff-bf3cadce6b99
-- title:
--   Planar supergraph augmentation edge bound
-- statement:
--   Every drawable simple graph on at least three finite ordered vertices has a drawable supergraph on the same vertex type with at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_with_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V,
      J ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
