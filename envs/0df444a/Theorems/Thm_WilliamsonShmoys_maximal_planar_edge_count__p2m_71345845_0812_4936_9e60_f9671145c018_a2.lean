-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_71345845_0812_4936_9e60_f9671145c018_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_71345845_0812_4936_9e60_f9671145c018_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:14:44.083034+00:00
-- url     : https://prove2.me/theorems/172f4409-2ccc-4845-8ec2-78e688ce1323
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly three times the vertex count minus six edges. The bound of at least three vertices is essential to this formula. A proof route is to use maximality to obtain a connected plane triangulation from the given drawing, then apply Euler’s formula and count edge incidences along face boundaries. The topological argument for the supplied drawing predicate is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_71345845_0812_4936_9e60_f9671145c018_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U = T) :
    (letI : DecidableRel T.Adj := Classical.decRel T.Adj;
     3 * Fintype.card V = T.edgeFinset.card + 6) := by
  sorry
