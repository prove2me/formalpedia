-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_planar_edge_upper_bound__p2m_4d55918f_bbf7_4f10_a854_239f6af3f8f1_a1
-- name    : WilliamsonShmoys.simple_planar_edge_upper_bound__p2m_4d55918f_bbf7_4f10_a854_239f6af3f8f1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T20:53:12.69562+00:00
-- url     : https://prove2.me/theorems/d921569a-2e61-4e68-b723-868e1c709ea4
-- title:
--   Simple planar graphs have at most 3|V|−6 edges
-- statement:
--   A finite simple graph with the supplied crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This isolates the planar Euler argument from connectivity and removes the geometric work from the parent. A concrete route is to interpret the injective vertex placement and noncrossing arcs as a plane embedding, augment the graph without adding vertices to a triangulation, apply Euler’s formula, and combine it with the fact that every face boundary has at least three edge incidences. The condition |V| ≥ 3 is essential to the stated bound and handles the small-size boundary; no connectedness assumption is needed for the planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.simple_planar_edge_upper_bound__p2m_4d55918f_bbf7_4f10_a854_239f6af3f8f1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
