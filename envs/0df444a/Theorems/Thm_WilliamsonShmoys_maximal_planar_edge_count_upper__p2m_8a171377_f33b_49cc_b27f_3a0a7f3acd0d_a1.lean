-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_8a171377_f33b_49cc_b27f_3a0a7f3acd0d_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_8a171377_f33b_49cc_b27f_3a0a7f3acd0d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:55:15.435251+00:00
-- url     : https://prove2.me/theorems/f1cbd61d-56d2-4b64-81ce-1556811a8e35
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Any finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This is the standard planar edge bound. A proof route is to extend the drawing to a connected plane graph, use Euler’s formula and the fact that each face boundary has length at least three, and handle disconnected graphs by planar augmentation or component accounting. This removes the upper-bound half of the target; the topological Euler argument remains to be formalized from the arc-based drawing definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_8a171377_f33b_49cc_b27f_3a0a7f3acd0d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 ≤ Fintype.card V) :
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  sorry
