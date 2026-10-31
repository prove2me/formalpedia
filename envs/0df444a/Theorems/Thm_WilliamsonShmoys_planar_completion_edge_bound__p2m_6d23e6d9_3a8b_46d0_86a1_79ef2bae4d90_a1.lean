-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_edge_bound__p2m_6d23e6d9_3a8b_46d0_86a1_79ef2bae4d90_a1
-- name    : WilliamsonShmoys.planar_completion_edge_bound__p2m_6d23e6d9_3a8b_46d0_86a1_79ef2bae4d90_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:01:33.369878+00:00
-- url     : https://prove2.me/theorems/a6f95464-e388-4a5e-9ab8-247431a72b86
-- title:
--   Planar completion reaches the triangulated edge bound
-- statement:
--   Every drawable simple graph on at least three fixed vertices is a subgraph of a drawable simple graph on the same vertices with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_edge_bound__p2m_6d23e6d9_3a8b_46d0_86a1_79ef2bae4d90_a1
    {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      3 * Fintype.card V - 6 ≤ Q.edgeSet.ncard := by sorry
