-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_a4df0fa7_688f_4bd0_bfe4_ea6603f7e8eb_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_bound__p2m_a4df0fa7_688f_4bd0_bfe4_ea6603f7e8eb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:46:38.896827+00:00
-- url     : https://prove2.me/theorems/46c30075-4bfd-440f-9130-4a3c3cfebadb
-- title:
--   Edge bound for a maximal drawn graph
-- statement:
--   A finite simple graph on at least three vertices that is maximal among graphs admitting the specified planar drawing has at most `3 * |V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_bound__p2m_a4df0fa7_688f_4bd0_bfe4_ea6603f7e8eb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      P.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ P.edgeSet) :
    P.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
