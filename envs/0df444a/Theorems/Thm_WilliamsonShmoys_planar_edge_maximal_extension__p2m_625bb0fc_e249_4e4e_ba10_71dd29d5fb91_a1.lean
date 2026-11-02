-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_extension__p2m_625bb0fc_e249_4e4e_ba10_71dd29d5fb91_a1
-- name    : WilliamsonShmoys.planar_edge_maximal_extension__p2m_625bb0fc_e249_4e4e_ba10_71dd29d5fb91_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:03:41.807511+00:00
-- url     : https://prove2.me/theorems/1025e42f-ede1-4af2-8086-d463e08e797e
-- title:
--   Extend a drawable graph to a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_maximal_extension__p2m_625bb0fc_e249_4e4e_ba10_71dd29d5fb91_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N := by sorry
