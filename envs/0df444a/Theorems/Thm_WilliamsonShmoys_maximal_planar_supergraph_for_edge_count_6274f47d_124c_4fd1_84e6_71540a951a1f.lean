-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_for_edge_count_6274f47d_124c_4fd1_84e6_71540a951a1f
-- name    : WilliamsonShmoys.maximal_planar_supergraph_for_edge_count_6274f47d_124c_4fd1_84e6_71540a951a1f
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:02:49.605742+00:00
-- url     : https://prove2.me/theorems/29d717a9-43c6-4046-ae9a-0f7c63322509
-- title:
--   A finite drawable graph has an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph on the same vertices that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_for_edge_count_6274f47d_124c_4fd1_84e6_71540a951a1f
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hPlanar : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ M : SimpleGraph V,
        K.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M = K := by sorry
