-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_triangulation__p2m_e279d529_0df7_4422_b7c0_ab730b7394ba_a1
-- name    : WilliamsonShmoys.planar_edge_augmentation_triangulation__p2m_e279d529_0df7_4422_b7c0_ab730b7394ba_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T12:39:37.191176+00:00
-- url     : https://prove2.me/theorems/21bb6f97-2922-436c-8d92-71f0b7399afd
-- title:
--   Extend a planar drawing to a triangulation
-- statement:
--   Extend the given planar drawing, on the same finite vertex set, to a planar supergraph with exactly 3|V|−6 edges. For |V|≥3, the route is to insert noncrossing edges until the drawing is maximal, then establish that every face of the resulting maximal simple planar graph is triangular and count its edges. This is the main topological obligation and must handle disconnected drawings as well as connected ones.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_augmentation_triangulation__p2m_e279d529_0df7_4422_b7c0_ab730b7394ba_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hE : K.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ T : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      K.edgeSet ⊆ T.edgeSet ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
