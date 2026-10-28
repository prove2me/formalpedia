-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:50:11.041718+00:00
-- url     : https://prove2.me/theorems/97cd64c7-e0e5-4118-aa09-45bcf318119e
-- title:
--   Every drawable graph has a maximal drawable supergraph on the same vertices
-- statement:
--   For every drawable graph K on a finite ordered vertex type, there is a drawable supergraph H on the same vertices that contains K, has at least as many edges, and has no strictly larger drawable supergraph on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ J : SimpleGraph V,
        H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) := by sorry
