-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_1591b9cd_ac13_4639_82d2_61e7ddbdd660
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_1591b9cd_ac13_4639_82d2_61e7ddbdd660
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:37:18.147346+00:00
-- url     : https://prove2.me/theorems/f877e9d9-1507-4964-b363-716cd8823548
-- title:
--   Extend a drawable graph to a maximal drawable supergraph
-- statement:
--   A drawable graph on a finite vertex type has a drawable supergraph that is maximal under inclusion and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_1591b9cd_ac13_4639_82d2_61e7ddbdd660
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H) ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
