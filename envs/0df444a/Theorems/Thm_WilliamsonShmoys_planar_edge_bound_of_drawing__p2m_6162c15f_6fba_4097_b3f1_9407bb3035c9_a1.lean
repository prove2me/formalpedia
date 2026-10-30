-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_drawing__p2m_6162c15f_6fba_4097_b3f1_9407bb3035c9_a1
-- name    : WilliamsonShmoys.planar_edge_bound_of_drawing__p2m_6162c15f_6fba_4097_b3f1_9407bb3035c9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T07:01:33.23459+00:00
-- url     : https://prove2.me/theorems/7ba85b8f-ff64-4712-bb70-3fc0e332b1b2
-- title:
--   Edge bound for any finite drawable simple graph
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has at most 3n − 6 edges. This stronger reusable result does not require edge maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Tactic
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_of_drawing__p2m_6162c15f_6fba_4097_b3f1_9407bb3035c9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
