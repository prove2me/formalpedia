-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_d8e86b30_fed1_4ee5_9c6d_8ff76555c4e7
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph_d8e86b30_fed1_4ee5_9c6d_8ff76555c4e7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:42:12.751993+00:00
-- url     : https://prove2.me/theorems/10b30a4f-2f8c-4286-9dc1-0777ebfa4fae
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph_d8e86b30_fed1_4ee5_9c6d_8ff76555c4e7
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V, Q ≤ R ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      ∀ S : SimpleGraph V, R ≤ S →
        WilliamsonShmoys.HasPlanarDrawingOn S → S = R := by sorry
