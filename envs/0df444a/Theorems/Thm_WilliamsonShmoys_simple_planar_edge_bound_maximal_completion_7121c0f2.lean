-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound_maximal_completion_7121c0f2
-- name    : WilliamsonShmoys.simple_planar_edge_bound_maximal_completion_7121c0f2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:01:22.815409+00:00
-- url     : https://prove2.me/theorems/d15c2c44-e100-4fbb-9381-8a66f7fdc7cb
-- title:
--   Completion to a maximal drawable supergraph
-- statement:
--   Extend the given drawable graph to one maximal among drawable supergraphs on the same finite vertex type, preserving the vertex set and not decreasing the edge count. The finite maximization argument handles disconnected inputs as well.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.simple_planar_edge_bound_maximal_completion_7121c0f2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    Exists fun H : SimpleGraph V =>
      K <= H /\
      K.edgeSet.ncard <= H.edgeSet.ncard /\
      WilliamsonShmoys.HasPlanarDrawingOn H /\
      (forall J : SimpleGraph V, H <= J ->
        WilliamsonShmoys.HasPlanarDrawingOn J -> J <= H) := by sorry
