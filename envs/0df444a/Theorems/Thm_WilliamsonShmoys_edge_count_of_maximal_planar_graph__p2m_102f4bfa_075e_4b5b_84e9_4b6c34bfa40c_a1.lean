-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_graph__p2m_102f4bfa_075e_4b5b_84e9_4b6c34bfa40c_a1
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_graph__p2m_102f4bfa_075e_4b5b_84e9_4b6c34bfa40c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:11:19.115277+00:00
-- url     : https://prove2.me/theorems/4d6cc368-2e2c-4152-a841-fdbbad35330d
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A drawable graph on at least three vertices whose edge count is maximal among drawable supergraphs on the same vertices has exactly 3|V|−6 edges. The proof route is to derive connectedness and triangular faces from maximality and apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.edge_count_of_maximal_planar_graph__p2m_102f4bfa_075e_4b5b_84e9_4b6c34bfa40c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hmax : ∀ Q : SimpleGraph V,
      (∀ u v, P.Adj u v → Q.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn Q →
      Q.edgeSet.ncard ≤ P.edgeSet.ncard) :
    3 * Fintype.card V = P.edgeSet.ncard + 6 := by
  sorry
