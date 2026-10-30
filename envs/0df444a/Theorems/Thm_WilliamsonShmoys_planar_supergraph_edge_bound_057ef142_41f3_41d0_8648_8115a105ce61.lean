-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_bound_057ef142_41f3_41d0_8648_8115a105ce61
-- name    : WilliamsonShmoys.planar_supergraph_edge_bound_057ef142_41f3_41d0_8648_8115a105ce61
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:07:40.017738+00:00
-- url     : https://prove2.me/theorems/3624186a-b460-4cf9-8afd-86ec1a2d5ee8
-- title:
--   Planar supergraph with the planar lower edge bound
-- statement:
--   Every drawable finite simple graph on at least three vertices is a subgraph, on the same vertex type, of a drawable graph with at least 3|V|−6 edges. The order hypothesis is needed for the planar lower edge bound and includes the boundary case of exactly three vertices. This isolates the geometric augmentation and planar counting work from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_edge_bound_057ef142_41f3_41d0_8648_8115a105ce61
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      Set.Subset M.edgeSet N.edgeSet ∧
      3 * Fintype.card V <= N.edgeSet.ncard + 6 := by sorry
