-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_exact_edge_count__p2m_8ea6d6e0_f206_47b7_9e0b_83b7a69a6862_a2
-- name    : WilliamsonShmoys.planar_supergraph_exact_edge_count__p2m_8ea6d6e0_f206_47b7_9e0b_83b7a69a6862_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:06:34.689337+00:00
-- url     : https://prove2.me/theorems/adb36ea0-1077-447f-b2c5-a4177e2cdb6e
-- title:
--   Planar supergraph with exact maximal edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges. This isolates planar completion and the Euler face-count argument from the parent. A proof route is to add noncrossing edges until every face is triangular, then combine Euler’s formula with face-edge incidence counting. The remaining core obligation is proving that completion for the supplied drawing predicate; the n=3 boundary case is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_exact_edge_count__p2m_8ea6d6e0_f206_47b7_9e0b_83b7a69a6862_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, HasPlanarDrawingOn K ∧
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
        3 * Fintype.card V = K.edgeFinset.card + 6) := by sorry
