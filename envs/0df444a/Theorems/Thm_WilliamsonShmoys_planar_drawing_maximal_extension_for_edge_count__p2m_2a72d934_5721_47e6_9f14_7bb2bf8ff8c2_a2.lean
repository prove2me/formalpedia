-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_count__p2m_2a72d934_5721_47e6_9f14_7bb2bf8ff8c2_a2
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count__p2m_2a72d934_5721_47e6_9f14_7bb2bf8ff8c2_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T11:48:48.801033+00:00
-- url     : https://prove2.me/theorems/fd1925df-0d55-4740-aaf1-fdb211fb2361
-- title:
--   Maximal drawable extension on a fixed vertex set
-- statement:
--   Every drawable graph on a fixed finite ordered vertex type has a drawable supergraph maximal under edge inclusion, with at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count__p2m_2a72d934_5721_47e6_9f14_7bb2bf8ff8c2_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      K.edgeSet.ncard ≤ L.edgeSet.ncard ∧
      ∀ M : SimpleGraph V,
        L.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet ⊆ L.edgeSet := by sorry
