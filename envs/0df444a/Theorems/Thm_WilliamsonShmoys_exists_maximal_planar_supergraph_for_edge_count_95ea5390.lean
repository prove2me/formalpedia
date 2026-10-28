-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_count_95ea5390
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_count_95ea5390
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T17:27:38.279873+00:00
-- url     : https://prove2.me/theorems/ea70155f-1321-4520-b185-7c70765db55e
-- title:
--   A maximal drawable supergraph exists on a finite vertex type
-- statement:
--   Among the finitely many drawable supergraphs of L on the fixed finite vertex type, choose one with maximum edge-set cardinality. It is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_count_95ea5390
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, M ≤ N →
          WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by sorry
