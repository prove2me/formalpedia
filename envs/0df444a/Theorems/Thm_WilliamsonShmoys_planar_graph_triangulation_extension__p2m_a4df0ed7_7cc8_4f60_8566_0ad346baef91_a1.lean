-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_extension__p2m_a4df0ed7_7cc8_4f60_8566_0ad346baef91_a1
-- name    : WilliamsonShmoys.planar_graph_triangulation_extension__p2m_a4df0ed7_7cc8_4f60_8566_0ad346baef91_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:56:23.471246+00:00
-- url     : https://prove2.me/theorems/a419e21a-2978-404e-8b1f-5dd1d0da8bd8
-- title:
--   Extend a planar drawing to a triangulation
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_triangulation_extension__p2m_a4df0ed7_7cc8_4f60_8566_0ad346baef91_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
