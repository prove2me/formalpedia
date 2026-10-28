-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_count_c4011bda
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_count_c4011bda
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T12:42:58.828037+00:00
-- url     : https://prove2.me/theorems/96e44785-45cc-4173-9093-6e1ca7afa8f7
-- title:
--   Every drawable finite graph has a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph is contained in a drawable supergraph that is maximal under inclusion among drawable graphs on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_count_c4011bda
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ T : SimpleGraph V,
      L ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
        ∀ S : SimpleGraph V,
          WilliamsonShmoys.HasPlanarDrawingOn S → T ≤ S → S ≤ T := by sorry
