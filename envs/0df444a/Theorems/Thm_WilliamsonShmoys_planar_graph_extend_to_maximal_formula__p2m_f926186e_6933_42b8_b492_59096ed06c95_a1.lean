-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_extend_to_maximal_formula__p2m_f926186e_6933_42b8_b492_59096ed06c95_a1
-- name    : WilliamsonShmoys.planar_graph_extend_to_maximal_formula__p2m_f926186e_6933_42b8_b492_59096ed06c95_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:32:47.218521+00:00
-- url     : https://prove2.me/theorems/c6e7e4d2-ca9d-4ea4-bf6c-d30cb8b5a12f
-- title:
--   Extend a planar drawing to the maximal planar edge count
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type of size at least three extends to a drawable supergraph on the same vertices whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_extend_to_maximal_formula__p2m_f926186e_6933_42b8_b492_59096ed06c95_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hcard : LE.le 3 (Fintype.card V)) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      (letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
        fun K => Classical.decRel K.Adj
       N.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
