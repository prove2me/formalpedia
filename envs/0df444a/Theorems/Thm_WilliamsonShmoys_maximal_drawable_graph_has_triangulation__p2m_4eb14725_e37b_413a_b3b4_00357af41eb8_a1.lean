-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulation__p2m_4eb14725_e37b_413a_b3b4_00357af41eb8_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_triangulation__p2m_4eb14725_e37b_413a_b3b4_00357af41eb8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:14:53.595797+00:00
-- url     : https://prove2.me/theorems/d5177853-4df8-41a7-94e3-cb1253738394
-- title:
--   Every finite drawable graph extends to a triangulation
-- statement:
--   Any drawable finite simple graph on at least three vertices is a subgraph of a drawable graph on the same vertices whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_has_triangulation__p2m_4eb14725_e37b_413a_b3b4_00357af41eb8_a1 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) [DecidableRel N.Adj] (hcard : 3 ≤ Fintype.card V) (hN : HasPlanarDrawingOn N) : ∃ P : SimpleGraph V, N ≤ P ∧ HasPlanarDrawingOn P ∧ ∀ [DecidableRel P.Adj], P.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
