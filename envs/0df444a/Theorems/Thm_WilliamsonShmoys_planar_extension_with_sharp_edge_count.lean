-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_with_sharp_edge_count
-- name    : WilliamsonShmoys.planar_extension_with_sharp_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:25:09.790032+00:00
-- url     : https://prove2.me/theorems/16efa91f-ea17-4fca-8681-329f091064c3
-- title:
--   Planar extension with the sharp edge count
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex type with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_with_sharp_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    exists M : SimpleGraph V, L <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
