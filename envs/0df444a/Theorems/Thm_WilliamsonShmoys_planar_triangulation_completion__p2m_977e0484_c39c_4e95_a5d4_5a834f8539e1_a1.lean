-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_977e0484_c39c_4e95_a5d4_5a834f8539e1_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_977e0484_c39c_4e95_a5d4_5a834f8539e1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:41:04.856045+00:00
-- url     : https://prove2.me/theorems/b6e1b838-6a07-4127-97a1-2301fa6a9ddd
-- title:
--   Completion of a drawable graph to an extremal planar graph
-- statement:
--   Every drawable finite simple graph on at least three vertices is contained in a drawable graph on the same vertices with exactly 3|V|−6 edges. This removes the topological completion and edge-count argument from the parent. A proof route is to extend the drawing to a maximal planar graph, show its faces are triangles using planar embedding theory, and apply Euler’s formula; the three-vertex case completes to the triangle. The remaining core obligation is formalizing these facts for the supplied arc-based drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_977e0484_c39c_4e95_a5d4_5a834f8539e1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       N.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
