-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_6d98c2a3_7d62_42a8_a794_93d41b1b40ef_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_6d98c2a3_7d62_42a8_a794_93d41b1b40ef_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:52:20.929555+00:00
-- url     : https://prove2.me/theorems/3ea6bb1c-a422-4d1c-b17f-ef9a0e48b692
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no drawable strict supergraph on the same vertices has exactly 3|V|−6 edges. The proof route is to show maximality forces every face to be triangular, then apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_6d98c2a3_7d62_42a8_a794_93d41b1b40ef_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K)
    (hV : 3 ≤ Fintype.card V) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    letI : Fintype ↥K.edgeSet := Fintype.ofFinite _
    K.edgeFinset.card + 6 = 3 * Fintype.card V := by
  sorry
