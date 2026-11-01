-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound__p2m_b3b14217_54f7_4da9_9b6d_f0fddbb566d2_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_b3b14217_54f7_4da9_9b6d_f0fddbb566d2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:38:56.254204+00:00
-- url     : https://prove2.me/theorems/e23427be-8e8a-4c77-a28e-0966a53f4506
-- title:
--   Planar simple graph edge bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most three times its number of vertices minus six edges. The Lean form uses the equivalent natural-number inequality `edgeSet.ncard + 6 ≤ 3 * card V`. Prove this using Euler’s formula and the lower bound of three on face-boundary lengths, with the small-vertex case handled under the stated hypothesis.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_b3b14217_54f7_4da9_9b6d_f0fddbb566d2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
